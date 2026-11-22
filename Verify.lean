import BSD
import Lean.Util.CollectAxioms

/-! Replayable checks of the target type, local normalizations and axiom dependencies. -/

open BSD BSD.FermatCubic

example : RankConjecture ↔
    ∀ E : WeierstrassCurve ℚ, E.IsElliptic →
      ∃ L : ℂ → ℂ, (Meromorphic L ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s) ∧
        meromorphicOrderAt L 1 = Module.finrank ℤ E.toAffine.Point := Iff.rfl

example : Nat.card curve.toAffine.Point = 3 := rational_point_count
example : Module.finrank ℤ curve.toAffine.Point = 0 := algebraic_rank_zero
example : etaL 1 ≠ 0 := etaL_one_ne_zero
example : RankPart (⟨0, 0, 0, 0, -432⟩ : WeierstrassCurve ℚ) := weakBSD

#print axioms BSD.FermatCubic.weakBSD

example : primaryTrace 7 = -1 := by
  simpa using primaryTrace_eq (p := 7) (a := 1) (b := 3) (by decide)
    (by norm_num) (by decide) (by decide)

example : primaryTrace 13 = 5 := by
  simpa using primaryTrace_eq (p := 13) (a := 4) (b := 3) (by decide)
    (by norm_num) (by decide) (by decide)

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut modules : NameSet := {}
  let mut used : NameSet := {}
  for (name, info) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx]!
    unless (`BSD).isPrefixOf mod do continue
    modules := modules.insert mod
    if let .axiomInfo _ := info then
      throwError "Unexpected project axiom {name} in {mod}"
    if let .thmInfo _ := info then
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in theorem {name}"
        used := used.insert ax
      checked := checked + 1
  if checked = 0 then throwError "No project theorems were checked"
  logInfo m!"Checked {checked} theorem declarations in {modules.toList.length} modules with declarations. Axioms used: {used.toList}."
