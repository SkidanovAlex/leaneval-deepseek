import Mathlib
import Submission.Work.Pi6.EMM2.Statements
import Submission.Work.Pi6.EMM2.SerreKit
import Submission.Work.Cohomology.contractible
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# Shared vocabulary for the `K(ℤ/2,4)` forcing argument (`Work.Pi6.EMM2.k4forcing9`)

The path–loop fibration `ΩX → PX → X` of a based space `X` is the setup of every forcing argument
of area EMM2.  This module fixes the names (`k4PathSpace`, `k4PathFib`, `k4PathBase`,
`k4LoopSpace`, `k4LoopBase`, `k4LoopIncl`) and collects the elementary lemmas about `finrank`,
`IsZero`, the `e₂`-isomorphism and the unit that the argument uses.  It is deliberately small and
stable: the child lemmas of `Pi6/EMM2/K4F/…` import it.
-/

namespace Work.Pi6.EMM2

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {𝕜 : Type} [Field 𝕜]

/-! ## The path–loop fibration -/

/-- The total space `PX` of the path fibration of `X` at `x₀`. -/
abbrev k4PathSpace {X : Type} [TopologicalSpace X] (x₀ : X) : Type :=
  Work.Serre.mpath (ContinuousMap.const PUnit x₀)

/-- The path fibration `p : PX → X`. -/
abbrev k4PathFib {X : Type} [TopologicalSpace X] (x₀ : X) : C(k4PathSpace x₀, X) :=
  Work.Serre.mpathQ (ContinuousMap.const PUnit x₀)

/-- The base point of `PX`. -/
abbrev k4PathBase {X : Type} [TopologicalSpace X] (x₀ : X) : k4PathSpace x₀ :=
  Work.Serre.mpathOf (ContinuousMap.const PUnit x₀) PUnit.unit

/-- The fibre `ΩX` of the path fibration (based loops at `x₀`). -/
abbrev k4LoopSpace {X : Type} [TopologicalSpace X] (x₀ : X) : Type :=
  Fib (k4PathFib x₀) (k4PathBase x₀)

/-- The base point of the loop space. -/
abbrev k4LoopBase {X : Type} [TopologicalSpace X] (x₀ : X) : k4LoopSpace x₀ :=
  Work.StemsB.fibrePoint (k4PathFib x₀) (k4PathBase x₀)

/-- The inclusion of the loop space into the path space. -/
abbrev k4LoopIncl {X : Type} [TopologicalSpace X] (x₀ : X) : C(k4LoopSpace x₀, k4PathSpace x₀) :=
  Work.StemsB.fibreIncl (k4PathFib x₀) ((k4PathFib x₀) (k4PathBase x₀))

/-! ## Elementary facts about `finrank` and `IsZero` -/

/-- The unit of `H⁰` is nonzero when `H⁰` is one-dimensional. -/
theorem k4_one_ne_zero {Y : Type} [TopologicalSpace Y]
    (h0 : Module.finrank 𝕜 (Coh 𝕜 Y 0) = 1) : one 𝕜 Y ≠ 0 := by
  intro hone
  have hsub : Subsingleton (Coh 𝕜 Y 0) := ⟨fun a b => by
    have ha : cup 𝕜 Y 0 0 (one 𝕜 Y) a = a := by
      show ((Work.Cohomology.cupH' 𝕜 (TopCat.toSSet.obj (TopCat.of Y)) 0 0)
        (Work.Cohomology.oneH 𝕜 (TopCat.toSSet.obj (TopCat.of Y)))) a = a
      exact Work.Cohomology.cupH'_one_left 𝕜 (TopCat.toSSet.obj (TopCat.of Y)) 0 a
    have hb : cup 𝕜 Y 0 0 (one 𝕜 Y) b = b := by
      show ((Work.Cohomology.cupH' 𝕜 (TopCat.toSSet.obj (TopCat.of Y)) 0 0)
        (Work.Cohomology.oneH 𝕜 (TopCat.toSSet.obj (TopCat.of Y)))) b = b
      exact Work.Cohomology.cupH'_one_left 𝕜 (TopCat.toSSet.obj (TopCat.of Y)) 0 b
    rw [← ha, ← hb, hone]
    simp⟩
  have hfd : FiniteDimensional 𝕜 (Coh 𝕜 Y 0) :=
    FiniteDimensional.of_finrank_pos (by rw [h0]; norm_num)
  rw [Module.finrank_zero_iff.mpr hsub] at h0
  omega

/-- A module of dimension one has a nonzero element. -/
theorem k4_exists_ne_zero {M : Type} [AddCommGroup M] [Module 𝕜 M]
    (h : Module.finrank 𝕜 M = 1) : ∃ x : M, x ≠ 0 := by
  by_contra hc
  push Not at hc
  have hsub : Subsingleton M := ⟨fun a b => by rw [hc a, hc b]⟩
  have hfd : FiniteDimensional 𝕜 M := FiniteDimensional.of_finrank_pos (by rw [h]; norm_num)
  rw [Module.finrank_zero_iff.mpr hsub] at h
  omega

/-- A module of dimension zero is a subsingleton. -/
theorem k4_subsingleton_of_finrank_zero {M : Type} [AddCommGroup M] [Module 𝕜 M]
    [FiniteDimensional 𝕜 M] (h : Module.finrank 𝕜 M = 0) : Subsingleton M :=
  Module.finrank_zero_iff.mp h

/-- The dimension of a zero module is zero. -/
theorem k4_finrank_eq_zero_of_isZero {M : Type} [AddCommGroup M] [Module 𝕜 M]
    (h : IsZero (ModuleCat.of 𝕜 M)) : Module.finrank 𝕜 M = 0 := by
  haveI : Subsingleton (ModuleCat.of 𝕜 M) := ModuleCat.subsingleton_of_isZero h
  exact Module.finrank_eq_zero_of_subsingleton 𝕜 M

/-- The dimension of a vanishing cohomology group is zero. -/
theorem k4_finrank_eq_zero_of_isZero_cohom {Y : Type} [TopologicalSpace Y] {n : ℕ}
    (h : IsZero (Coh 𝕜 Y n)) : Module.finrank 𝕜 (Coh 𝕜 Y n) = 0 := by
  haveI : Subsingleton (Coh 𝕜 Y n) := ModuleCat.subsingleton_of_isZero h
  exact Module.finrank_eq_zero_of_subsingleton 𝕜 (Coh 𝕜 Y n)

/-- `IsZero` of a module from `Subsingleton` of the underlying type. -/
theorem k4_isZero_of_subsingleton {M : Type} [AddCommGroup M] [Module 𝕜 M]
    [Subsingleton M] : IsZero (ModuleCat.of 𝕜 M) :=
  ModuleCat.isZero_of_subsingleton _

/-- A nonzero element of a module gives a positive dimension. -/
theorem k4_finrank_pos_of_ne_zero {M : Type} [AddCommGroup M] [Module 𝕜 M]
    [FiniteDimensional 𝕜 M] {x : M} (hx : x ≠ 0) : 0 < Module.finrank 𝕜 M :=
  Module.finrank_pos_iff.mpr ⟨x, 0, hx⟩

/-- Monotonicity of `IsEMSpaceUpTo` in the range. -/
theorem k4_isEMSpaceUpTo_mono {A : Type} [AddCommGroup A] {m : ℕ} (hm : 0 < m) {M M' : ℕ}
    {X : Type} [TopologicalSpace X] {x : X} (h : Work.Serre.IsEMSpaceUpTo A m hm M X x)
    (hM : M' ≤ M) : Work.Serre.IsEMSpaceUpTo A m hm M' X x :=
  ⟨h.1, fun i hi hc => h.2 i hi (hc.imp id (fun hle => le_trans hle hM))⟩

/-- A module isomorphism applied to the inverse. -/
theorem k4_iso_hom_inv_hom_apply {M N : ModuleCat 𝕜} (e : M ≅ N) (y : N) :
    e.hom (e.inv.hom y) = y := by
  have h := e.toLinearEquiv.apply_symm_apply y
  simpa using h

/-- The inverse of a module isomorphism applied to the image. -/
theorem k4_iso_inv_hom_apply {M N : ModuleCat 𝕜} (e : M ≅ N) (x : M) :
    e.inv.hom (e.hom x) = x := by
  have h := e.toLinearEquiv.symm_apply_apply x
  simpa using h

/-! ## The `E₂` page -/

section E2

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E)

/-- The `e₂`-preimage of a pure tensor of nonzero classes is nonzero. -/
theorem k4_e2_inv_tmul_ne_zero (S : CohSS 𝕜) {s q : ℕ}
    (e2 : S.E 2 ((s : ℤ), (q : ℤ)) ≅
      ModuleCat.of 𝕜 (TensorProduct 𝕜 (Coh 𝕜 B s) (Coh 𝕜 (Fib p e₀) q)))
    {b : Coh 𝕜 B s} {f : Coh 𝕜 (Fib p e₀) q} (hb : b ≠ 0) (hf : f ≠ 0) :
    e2.inv.hom (b ⊗ₜ[𝕜] f) ≠ 0 := by
  intro hzero
  have h := k4_iso_hom_inv_hom_apply e2 (b ⊗ₜ[𝕜] f)
  rw [hzero, map_zero] at h
  exact tmul_ne_zero_of_ne_zero hb hf h.symm

/-- `E₂^{s,q}` vanishes when the base group `H^s(B)` does. -/
theorem k4_isZero_E2_left (S : CohSS 𝕜) (N : ℕ) (hS : IsSerreMSS S p e₀ N) {s q : ℕ}
    (hs : s ≤ N) (hq : q ≤ N) (h : IsZero (Coh 𝕜 B s)) :
    IsZero (S.E 2 ((s : ℤ), (q : ℤ))) := by
  obtain ⟨e2, _⟩ := hS
  haveI : Subsingleton (Coh 𝕜 B s) := ModuleCat.subsingleton_of_isZero h
  exact IsZero.of_iso (k4_isZero_of_subsingleton (𝕜 := 𝕜)
    (M := TensorProduct 𝕜 (Coh 𝕜 B s) (Coh 𝕜 (Fib p e₀) q))) (e2 s q hs hq)

/-- `E₂^{s,q}` vanishes when the fibre group `H^q(F)` does. -/
theorem k4_isZero_E2_right (S : CohSS 𝕜) (N : ℕ) (hS : IsSerreMSS S p e₀ N) {s q : ℕ}
    (hs : s ≤ N) (hq : q ≤ N) (h : IsZero (Coh 𝕜 (Fib p e₀) q)) :
    IsZero (S.E 2 ((s : ℤ), (q : ℤ))) := by
  obtain ⟨e2, _⟩ := hS
  haveI : Subsingleton (Coh 𝕜 (Fib p e₀) q) := ModuleCat.subsingleton_of_isZero h
  exact IsZero.of_iso (k4_isZero_of_subsingleton (𝕜 := 𝕜)
    (M := TensorProduct 𝕜 (Coh 𝕜 B s) (Coh 𝕜 (Fib p e₀) q))) (e2 s q hs hq)

/-- Vanishing of `E₂^a` propagates to every page `r ≥ 2`. -/
theorem k4_isZero_E_of_isZero_E2 (S : CohSS 𝕜) {a : ℤ × ℤ} (h : IsZero (S.E 2 a))
    {r : ℕ} (hr : 2 ≤ r) : IsZero (S.E r a) := by
  have h2 := S.isZero_two_of a h (r - 2)
  rwa [show r - 2 + 2 = r from by omega] at h2

end E2

end

end Work.Pi6.EMM2
