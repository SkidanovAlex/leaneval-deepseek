import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseBoxFock.KafzGauge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.GaugeWt` — gauge homogeneity ("weight") of the Fock words

The particle-number gauge `gaugeC X u` (KafzGauge) multiplies the Fock monomial `β` by
`u ^ (-(Σ β))`; consequently

    `gaugeC X u (annC X j w) = u • annC X j (gaugeC X u w)`,
    `gaugeC X u (creC X j w) = u⁻¹ • creC X j (gaugeC X u w)`,

so a word with `a` annihilations and `c` creations acquires the phase `u ^ (a - c)`.
This file turns that into the predicate

    `GaugeWt u A n : Prop := ∀ w, gaugeC X u (A w) = u ^ n • A (gaugeC X u w)`

and computes the weight of every spectator word appearing in the dictionary
`KvecF` of `Work.BoseBoxFock.KafzDict` (`annOfE`, `creOfE`, `nmF`, `Bgap`, `Bkin`,
`BW`, `Bbog1`, `Bbog2`, `BchiC`, `BchiA`, `BQ3a`, `BQ3b`), together with the
structural lemmas (`zero`, `one`, `add`, `sum`, `smul`, `neg`, `comp`) that make the
per-slot weights of `KvecF` immediate.

The weights of the 25 dictionary slots (`KvecF i`, weight `qvecF i - pvecF i`) are
proved in `Submission/Work/BoseBoxFock/GaugeWtKvecF.lean`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

variable {m : ℕ} [NeZero m]

/-! ## 1. The ladder operators on the `Finsupp` core, on basis vectors -/

/-- `annF X j` on a basis vector: it lowers the `j`-occupation, gaining the weight
`√(γ j)`.  (Same as `Work.BoseB4.annF_single`, with the two scalars in the other order,
which is the form in which the gauge computation below produces it.) -/
lemma gauge_annF_single {X : Type*} [DecidableEq X] (j : X) (γ : X →₀ ℕ) (c : ℂ) :
    annF X j (Finsupp.single γ c)
      = ((Real.sqrt ((γ j : ℝ)) : ℂ) * c) •
          Finsupp.single (γ - Finsupp.single j 1) (1 : ℂ) := by
  rw [annF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, smul_smul, mul_comm]

/-- `creF X j` on a basis vector: it raises the `j`-occupation, gaining the weight
`√(γ j + 1)`. -/
lemma gauge_creF_single {X : Type*} [DecidableEq X] (j : X) (γ : X →₀ ℕ) (c : ℂ) :
    creF X j (Finsupp.single γ c)
      = ((Real.sqrt ((γ j : ℝ) + 1) : ℂ) * c) •
          Finsupp.single (γ + Finsupp.single j 1) (1 : ℂ) := by
  rw [creF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, smul_smul, mul_comm]

/-- Lowering the occupation of a nonempty mode lowers the total occupation by one. -/
lemma gauge_sum_sub_single {X : Type*} [DecidableEq X] (α : X →₀ ℕ) (k : X)
    (h : α k ≠ 0) :
    (α - Finsupp.single k 1).sum (fun _ j => j) = α.sum (fun _ j => j) - 1 := by
  have hsub : α - Finsupp.single k 1 = α.update k (α k - 1) := by
    ext j
    rw [Finsupp.tsub_apply, Finsupp.update_apply]
    by_cases hj : j = k
    · subst hj; simp
    · rw [Finsupp.single_eq_of_ne hj]; simp [hj]
  rw [hsub]
  have hsu : (α.update k (α k - 1)).sum (fun _ j => j) + α k
      = α.sum (fun _ j => j) + (α k - 1) := by
    have := Finsupp.sum_update_add α k (α k - 1) (fun _ j => j)
      (by intro i; rfl) (by intro i a b; rfl)
    simpa using this
  omega

/-- Raising the occupation of a mode raises the total occupation by one. -/
lemma gauge_sum_add_single {X : Type*} [DecidableEq X] (α : X →₀ ℕ) (k : X) :
    (α + Finsupp.single k 1).sum (fun _ j => j) = α.sum (fun _ j => j) + 1 := by
  have h := Finsupp.sum_add_index (f := α) (g := Finsupp.single k 1) (h := fun _ j => j)
    (by intro a ha; rfl) (by intro a ha b1 b2; rfl)
  have h2 : (Finsupp.single k (1 : ℕ)).sum (fun _ j => j) = 1 := by
    rw [Finsupp.sum_single_index (by rfl)]
  rw [h, h2]

/-! ## 2. `gaugeF` on the ladder operators -/

/-- `gaugeF` intertwines `annF j` with weight `u`. -/
theorem gaugeF_annF {X : Type*} [DecidableEq X] (u : ℂ) (hu : u ≠ 0) (j : X) :
    ∀ f : (X →₀ ℕ) →₀ ℂ, gaugeF X u (annF X j f) = u • annF X j (gaugeF X u f) := by
  intro f
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq, smul_add]
  | single γ c =>
      have hcoef : ((Real.sqrt ((γ j : ℝ)) : ℂ) * c)
            * u ^ (-(((γ - Finsupp.single j 1).sum fun _ k => k : ℕ) : ℤ))
          = u * ((u ^ (-(((γ.sum fun _ k => k : ℕ) : ℤ))) * c)
              * (Real.sqrt ((γ j : ℝ)) : ℂ)) := by
        rcases eq_or_ne (γ j) 0 with h | h
        · rw [h]; norm_num
        · have hjmem : j ∈ γ.support := Finsupp.mem_support_iff.mpr h
          have hpos : 1 ≤ γ.sum (fun _ k => k) := by
            rw [Finsupp.sum]
            calc (1 : ℕ) ≤ γ j := by omega
              _ = (fun _ k => k) j (γ j) := rfl
              _ ≤ ∑ x ∈ γ.support, (fun _ k => k) x (γ x) :=
                  Finset.single_le_sum (fun x _ => Nat.zero_le _) hjmem
          have hsub := gauge_sum_sub_single γ j h
          have hz : u ^ (-(((γ - Finsupp.single j 1).sum fun _ k => k : ℕ) : ℤ))
              = u * u ^ (-(((γ.sum fun _ k => k : ℕ) : ℤ))) := by
            rw [hsub]
            have hcast : (((γ.sum fun _ k => k) - 1 : ℕ) : ℤ)
                = ((γ.sum fun _ k => k : ℕ) : ℤ) - 1 := by omega
            rw [hcast]
            have : -(((γ.sum fun _ k => k : ℕ) : ℤ) - 1)
                = 1 + (-(((γ.sum fun _ k => k : ℕ) : ℤ))) := by ring
            rw [this, zpow_add₀ hu, zpow_one]
          rw [hz]; ring
      rw [gauge_annF_single, map_smul, gaugeF_single, gaugeF_single, map_smul,
        gauge_annF_single]
      simp only [mul_one, smul_smul]
      refine congrArg (fun z : ℂ =>
        z • (Finsupp.single (γ - Finsupp.single j 1) (1 : ℂ))) ?_
      show ((Real.sqrt ((γ j : ℝ)) : ℂ) * c)
            * u ^ (-(((γ - Finsupp.single j 1).sum fun _ k => k : ℕ) : ℤ))
          = u * ((u ^ (-(((γ.sum fun _ k => k : ℕ) : ℤ))) * c)
              * (Real.sqrt ((γ j : ℝ)) : ℂ))
      exact hcoef

/-- `gaugeF` intertwines `creF j` with weight `u⁻¹`. -/
theorem gaugeF_creF {X : Type*} [DecidableEq X] (u : ℂ) (hu : u ≠ 0) (j : X) :
    ∀ f : (X →₀ ℕ) →₀ ℂ, gaugeF X u (creF X j f) = u⁻¹ • creF X j (gaugeF X u f) := by
  intro f
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq, smul_add]
  | single γ c =>
      have hcoef : ((Real.sqrt ((γ j : ℝ) + 1) : ℂ) * c)
            * u ^ (-(((γ + Finsupp.single j 1).sum fun _ k => k : ℕ) : ℤ))
          = u⁻¹ * ((u ^ (-(((γ.sum fun _ k => k : ℕ) : ℤ))) * c)
              * (Real.sqrt ((γ j : ℝ) + 1) : ℂ)) := by
        have hadd := gauge_sum_add_single γ j
        have hz : u ^ (-(((γ + Finsupp.single j 1).sum fun _ k => k : ℕ) : ℤ))
            = u⁻¹ * u ^ (-(((γ.sum fun _ k => k : ℕ) : ℤ))) := by
          rw [hadd]
          have hcast : (((γ.sum fun _ k => k) + 1 : ℕ) : ℤ)
              = ((γ.sum fun _ k => k : ℕ) : ℤ) + 1 := by push_cast; ring
          rw [hcast]
          have : -(((γ.sum fun _ k => k : ℕ) : ℤ) + 1)
              = -1 + (-(((γ.sum fun _ k => k : ℕ) : ℤ))) := by ring
          rw [this, zpow_add₀ hu, zpow_neg_one]
        rw [hz]; ring
      rw [gauge_creF_single, map_smul, gaugeF_single, gaugeF_single, map_smul,
        gauge_creF_single]
      simp only [mul_one, smul_smul]
      refine congrArg (fun z : ℂ =>
        z • (Finsupp.single (γ + Finsupp.single j 1) (1 : ℂ))) ?_
      show ((Real.sqrt ((γ j : ℝ) + 1) : ℂ) * c)
            * u ^ (-(((γ + Finsupp.single j 1).sum fun _ k => k : ℕ) : ℤ))
          = u⁻¹ * ((u ^ (-(((γ.sum fun _ k => k : ℕ) : ℤ))) * c)
              * (Real.sqrt ((γ j : ℝ) + 1) : ℂ))
      exact hcoef

/-! ## 3. The gauge on the ladder operators of `cfock` -/

/-- The gauge intertwines `annC j` with weight `u`. -/
theorem gaugeC_annC {X : Type*} [DecidableEq X] (u : ℂ) (hu : u ≠ 0) (j : X)
    (w : cfock X) :
    gaugeC X u (annC X j w) = u • annC X j (gaugeC X u w) := by
  obtain ⟨f, rfl⟩ := (toCFock X).surjective w
  simp only [gaugeC, annC, LinearEquiv.coe_toLinearMap, LinearMap.comp_apply,
    LinearEquiv.symm_apply_apply]
  rw [gaugeF_annF (X := X) u hu j, map_smul]

/-- The gauge intertwines `creC j` with weight `u⁻¹`. -/
theorem gaugeC_creC {X : Type*} [DecidableEq X] (u : ℂ) (hu : u ≠ 0) (j : X)
    (w : cfock X) :
    gaugeC X u (creC X j w) = u⁻¹ • creC X j (gaugeC X u w) := by
  obtain ⟨f, rfl⟩ := (toCFock X).surjective w
  simp only [gaugeC, creC, LinearEquiv.coe_toLinearMap, LinearMap.comp_apply,
    LinearEquiv.symm_apply_apply]
  rw [gaugeF_creF (X := X) u hu j, map_smul]

/-! ## 4. The weight predicate -/

/-- **Gauge homogeneity.**  `GaugeWt u A n` is the pointwise identity
`gaugeC X u (A w) = u ^ n • A (gaugeC X u w)`, i.e. `A` intertwines the gauge with
weight `n`.  A word with `a` annihilations and `c` creations has weight `a - c`. -/
def GaugeWt {X : Type*} [DecidableEq X] (u : ℂ) (A : cfock X →ₗ[ℂ] cfock X) (n : ℤ) : Prop :=
  ∀ w : cfock X, gaugeC X u (A w) = u ^ n • A (gaugeC X u w)

/-- Restating a weight through an equality of exponents.  The weight of `hA` is
inferred first, so `n'` may be a numeral and `h` a concrete arithmetic fact. -/
theorem gaugeWt_of_eq {X : Type*} [DecidableEq X] {u : ℂ} {A : cfock X →ₗ[ℂ] cfock X}
    {n : ℤ} (hA : GaugeWt u A n) (n' : ℤ) (h : n = n') : GaugeWt u A n' := h ▸ hA

/-- Conjugating a weight along an equality of operators. -/
theorem gaugeWt_congr {X : Type*} [DecidableEq X] {u : ℂ} {A B : cfock X →ₗ[ℂ] cfock X}
    {n : ℤ} (hAB : A = B) (hA : GaugeWt u A n) : GaugeWt u B n := hAB ▸ hA

theorem gaugeWt_zero {X : Type*} [DecidableEq X] (u : ℂ) (n : ℤ) :
    GaugeWt u (0 : cfock X →ₗ[ℂ] cfock X) n := fun w => by simp

theorem gaugeWt_one {X : Type*} [DecidableEq X] (u : ℂ) :
    GaugeWt u (1 : cfock X →ₗ[ℂ] cfock X) 0 := fun w => by
  simp [Module.End.one_apply]

theorem gaugeWt_add {X : Type*} [DecidableEq X] {u : ℂ} {A B : cfock X →ₗ[ℂ] cfock X}
    {n : ℤ} (hA : GaugeWt u A n) (hB : GaugeWt u B n) : GaugeWt u (A + B) n := fun w => by
  rw [LinearMap.add_apply, map_add, hA w, hB w, LinearMap.add_apply, smul_add]

theorem gaugeWt_neg {X : Type*} [DecidableEq X] {u : ℂ} {A : cfock X →ₗ[ℂ] cfock X}
    {n : ℤ} (hA : GaugeWt u A n) : GaugeWt u (-A) n := fun w => by
  rw [LinearMap.neg_apply, map_neg, hA w, LinearMap.neg_apply, smul_neg]

theorem gaugeWt_sub {X : Type*} [DecidableEq X] {u : ℂ} {A B : cfock X →ₗ[ℂ] cfock X}
    {n : ℤ} (hA : GaugeWt u A n) (hB : GaugeWt u B n) : GaugeWt u (A - B) n := fun w => by
  rw [LinearMap.sub_apply, map_sub, hA w, hB w, LinearMap.sub_apply, smul_sub]

theorem gaugeWt_smul {X : Type*} [DecidableEq X] {u : ℂ} {A : cfock X →ₗ[ℂ] cfock X}
    {n : ℤ} (hA : GaugeWt u A n) (c : ℂ) : GaugeWt u (c • A) n := fun w => by
  rw [LinearMap.smul_apply, map_smul, hA w, LinearMap.smul_apply, smul_comm]

theorem gaugeWt_sum {X : Type*} [DecidableEq X] {u : ℂ} {ι : Type*} {n : ℤ}
    (s : Finset ι) (A : ι → cfock X →ₗ[ℂ] cfock X)
    (h : ∀ i ∈ s, GaugeWt u (A i) n) : GaugeWt u (∑ i ∈ s, A i) n := by
  intro w
  have hL : gaugeC X u ((∑ i ∈ s, A i) w) = ∑ i ∈ s, gaugeC X u (A i w) := by
    rw [LinearMap.sum_apply, map_sum]
  have hR : (∑ i ∈ s, A i) (gaugeC X u w) = ∑ i ∈ s, A i (gaugeC X u w) := by
    rw [LinearMap.sum_apply]
  rw [hL, hR, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i hi => h i hi w

/-- A finite linear combination of words of the same weight. -/
theorem gaugeWt_finset_smul {X : Type*} [DecidableEq X] {u : ℂ} {ι : Type*} {n : ℤ}
    (s : Finset ι) (c : ι → ℂ) (A : ι → cfock X →ₗ[ℂ] cfock X)
    (h : ∀ i ∈ s, GaugeWt u (A i) n) : GaugeWt u (∑ i ∈ s, c i • A i) n :=
  gaugeWt_sum s (fun i => c i • A i) fun i hi => gaugeWt_smul (h i hi) (c i)

theorem gaugeWt_comp {X : Type*} [DecidableEq X] {u : ℂ} (hu : u ≠ 0)
    {A B : cfock X →ₗ[ℂ] cfock X} {n m : ℤ}
    (hA : GaugeWt u A n) (hB : GaugeWt u B m) : GaugeWt u (A ∘ₗ B) (n + m) := fun w => by
  rw [LinearMap.comp_apply, hA (B w), hB w, map_smul, LinearMap.comp_apply, smul_smul,
    ← zpow_add₀ hu]

theorem gaugeWt_annC {X : Type*} [DecidableEq X] (u : ℂ) (hu : u ≠ 0) (j : X) :
    GaugeWt u (annC X j) 1 := fun w => by
  rw [gaugeC_annC (X := X) u hu j w, zpow_one]

theorem gaugeWt_creC {X : Type*} [DecidableEq X] (u : ℂ) (hu : u ≠ 0) (j : X) :
    GaugeWt u (creC X j) (-1) := fun w => by
  rw [gaugeC_creC (X := X) u hu j w, zpow_neg_one]

/-! ## 5. Weights of the spectator words of the dictionary -/

theorem gaugeWt_annOfE {u : ℂ} (hu : u ≠ 0) (φ : Fin m → ℝ) :
    GaugeWt u (annOfE (m := m) φ) 1 := by
  rw [annOfE]
  refine gaugeWt_finset_smul (Finset.univ : Finset (Excited m))
    (fun l : Excited m => ((φ l.1 : ℝ) : ℂ))
    (fun l : Excited m => annC (Excited m) l) fun l _ => ?_
  exact gaugeWt_annC u hu l

theorem gaugeWt_creOfE {u : ℂ} (hu : u ≠ 0) (φ : Fin m → ℝ) :
    GaugeWt u (creOfE (m := m) φ) (-1) := by
  rw [creOfE]
  refine gaugeWt_finset_smul (Finset.univ : Finset (Excited m))
    (fun l : Excited m => ((φ l.1 : ℝ) : ℂ))
    (fun l : Excited m => creC (Excited m) l) fun l _ => ?_
  exact gaugeWt_creC u hu l

theorem gaugeWt_nmF {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {u : ℂ} (hu : u ≠ 0) (f : Mode → Fin m → ℝ) (k : Mode) :
    GaugeWt u (nmF (m := m) f k) 0 := by
  rw [nmF]
  have h := gaugeWt_comp hu (gaugeWt_creOfE (m := m) hu (f k))
    (gaugeWt_annOfE (m := m) hu (f k))
  simpa using h

theorem gaugeWt_Bgap {u : ℂ} (hu : u ≠ 0) :
    GaugeWt u (Bgap (m := m)) 0 := by
  rw [Bgap]
  have h := gaugeWt_finset_smul (Finset.univ : Finset (Excited m))
    (fun _ : Excited m => (1 : ℂ))
    (fun l : Excited m => (creC (Excited m) l).comp (annC (Excited m) l))
    (fun l _ => gaugeWt_comp hu (gaugeWt_creC u hu l) (gaugeWt_annC u hu l))
  simpa using h

theorem gaugeWt_Bkin {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {u : ℂ} (hu : u ≠ 0) (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    GaugeWt u (Bkin (m := m) f E) 0 := by
  rw [Bkin]
  exact gaugeWt_finset_smul (Finset.univ : Finset Mode)
    (fun k : Mode => ((E.tau k : ℝ) : ℂ)) (fun k : Mode => nmF (m := m) f k)
    fun k _ => gaugeWt_nmF hu f k

theorem gaugeWt_BW {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {u : ℂ} (hu : u ≠ 0) (s : Finset Mode) (w : Mode → ℝ) (f : Mode → Fin m → ℝ) :
    GaugeWt u (BW (m := m) s w f) 0 := by
  rw [BW]
  exact gaugeWt_finset_smul s (fun k : Mode => ((w k : ℝ) : ℂ))
    (fun k : Mode => nmF (m := m) f k) fun k _ => gaugeWt_nmF hu f k

theorem gaugeWt_Bbog1 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {u : ℂ} (hu : u ≠ 0) (s : Finset Mode) (w : Mode → ℝ) (f : Mode → Fin m → ℝ) :
    GaugeWt u (Bbog1 (m := m) s w f) 2 := by
  rw [Bbog1]
  have h := gaugeWt_finset_smul s (fun k : Mode => ((w k : ℝ) : ℂ))
    (fun k : Mode => (annOfE (m := m) (f k)).comp (annOfE (m := m) (f (-k))))
    (fun k _ => gaugeWt_comp hu (gaugeWt_annOfE (m := m) hu (f k))
      (gaugeWt_annOfE (m := m) hu (f (-k))))
  simpa using h

theorem gaugeWt_Bbog2 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {u : ℂ} (hu : u ≠ 0) (s : Finset Mode) (w : Mode → ℝ) (f : Mode → Fin m → ℝ) :
    GaugeWt u (Bbog2 (m := m) s w f) (-2) := by
  rw [Bbog2]
  have h := gaugeWt_finset_smul s (fun k : Mode => ((w k : ℝ) : ℂ))
    (fun k : Mode => (creOfE (m := m) (f k)).comp (creOfE (m := m) (f (-k))))
    (fun k _ => gaugeWt_comp hu (gaugeWt_creOfE (m := m) hu (f k))
      (gaugeWt_creOfE (m := m) hu (f (-k))))
  simpa using h

theorem gaugeWt_BchiC {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {u : ℂ} (hu : u ≠ 0) (s : Finset Mode) (χ : Mode → ℝ) (c : ℝ)
    (φ : Mode → Fin m → ℝ) :
    GaugeWt u (BchiC (m := m) s χ c φ) (-1) := by
  rw [BchiC]
  exact gaugeWt_finset_smul s (fun k : Mode => (((c * χ k : ℝ)) : ℂ))
    (fun k : Mode => creOfE (m := m) (φ k)) fun k _ => gaugeWt_creOfE (m := m) hu (φ k)

theorem gaugeWt_BchiA {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {u : ℂ} (hu : u ≠ 0) (s : Finset Mode) (χ : Mode → ℝ) (c : ℝ)
    (φ : Mode → Fin m → ℝ) :
    GaugeWt u (BchiA (m := m) s χ c φ) 1 := by
  rw [BchiA]
  exact gaugeWt_finset_smul s (fun k : Mode => (((c * χ k : ℝ)) : ℂ))
    (fun k : Mode => annOfE (m := m) (φ k)) fun k _ => gaugeWt_annOfE (m := m) hu (φ k)

theorem gaugeWt_BQ3a {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {u : ℂ} (hu : u ≠ 0) (S Ks : Finset Mode) (γ : Mode → Mode → ℝ)
    (g f : Mode → Fin m → ℝ) :
    GaugeWt u (BQ3a (m := m) S Ks γ g f) 1 := by
  rw [BQ3a]
  have h := gaugeWt_sum S
    (fun s : Mode => ∑ k ∈ Ks, ((γ s k : ℝ) : ℂ) •
      ((creOfE (m := m) (g s)).comp
        ((annOfE (m := m) (f (s - k))).comp (annOfE (m := m) (f k)))))
    (fun s _ => gaugeWt_finset_smul Ks (fun k : Mode => ((γ s k : ℝ) : ℂ))
      (fun k : Mode => (creOfE (m := m) (g s)).comp
        ((annOfE (m := m) (f (s - k))).comp (annOfE (m := m) (f k))))
      (fun k _ => gaugeWt_comp hu (gaugeWt_creOfE (m := m) hu (g s))
        (gaugeWt_comp hu (gaugeWt_annOfE (m := m) hu (f (s - k)))
          (gaugeWt_annOfE (m := m) hu (f k)))))
  simpa using h

theorem gaugeWt_BQ3b {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {u : ℂ} (hu : u ≠ 0) (S Ks : Finset Mode) (γ : Mode → Mode → ℝ)
    (g f : Mode → Fin m → ℝ) :
    GaugeWt u (BQ3b (m := m) S Ks γ g f) (-1) := by
  rw [BQ3b]
  have h := gaugeWt_sum S
    (fun s : Mode => ∑ k ∈ Ks, ((γ s k : ℝ) : ℂ) •
      ((creOfE (m := m) (f k)).comp
        ((creOfE (m := m) (f (s - k))).comp (annOfE (m := m) (g s)))))
    (fun s _ => gaugeWt_finset_smul Ks (fun k : Mode => ((γ s k : ℝ) : ℂ))
      (fun k : Mode => (creOfE (m := m) (f k)).comp
        ((creOfE (m := m) (f (s - k))).comp (annOfE (m := m) (g s))))
      (fun k _ => gaugeWt_comp hu (gaugeWt_creOfE (m := m) hu (f k))
        (gaugeWt_comp hu (gaugeWt_creOfE (m := m) hu (f (s - k)))
          (gaugeWt_annOfE (m := m) hu (g s)))))
  simpa using h

/-- The weight of an operator commuting with the gauge is `0`. -/
theorem gaugeWt_of_comm {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {u : ℂ} {BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)}
    (hBNH : ∀ w : cfock (Excited m),
      gaugeC (Excited m) u (BNH w) = BNH (gaugeC (Excited m) u w)) :
    GaugeWt u BNH 0 := fun w => by rw [hBNH w, zpow_zero, one_smul]

end Work.BoseBoxFock
