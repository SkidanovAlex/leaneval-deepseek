import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLProd.aDiag_nsmul

/-!
# Exact `aDiag t`-invariance of the leafwise measures of a horospherical subgroup

Let `μ` be an `A`-invariant probability measure on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, let `T ≤ SL₃(ℝ)` be
horospherical (`IsHoro T`), and let `x ↦ νT x` be a system of leafwise measures for `T`
(`IsLeafwise μ T νT XT`, the frozen interface `P_Leafwise` enlarged).  Assume finally that the
diagonal element `a := aDiag t` **centralises** `T`, i.e. `a * g = g * a` for every `g ∈ T`.

Then `νT` is exactly invariant along the `a`-orbit, up to the `μ`-null set on which the leafwise
system is defined:

`∀ᵐ x ∂μ, νT (a ^ n • x) = νT x`.

This is step 2 of Pisa §8 (`Submission/Work/EKLComp/ProductPlan.md`).  The two ingredients are

* the `A`-covariance clause `(U7)` of `P_Leafwise`, which gives, for `μ`-a.e. `x`,
  `νT (a • x) = c • (νT x).map (g ↦ a * g * a⁻¹)` for some `c : ℝ≥0∞`, `c ≠ 0`, `c ≠ ⊤`;
* the fact that the conjugating map is the identity on `T`, which carries `νT x` because `a`
  centralises `T` (`map_conj_eq_of_carried_of_comm`);

so `νT (a • x) = c • νT x`, and the normalisation `νT (Box1 T) = 1` of the leafwise system forces
`c = 1`.  The general power `n` follows from `aDiag (n • t) = aDiag t ^ n`
(`Work.EKLProd.aDiag_nsmul`), since a power of an element centralising `T` still centralises `T`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLProd

open Work.EKLContract

/-! ## Two elementary tools -/

/-- A measure carried by a set `s` is unchanged by push-forward along a map that is the identity
on `s`.  (Only `ρ sᶜ = 0` and the pointwise identity on `s` are used; `f` need not be measurable,
as `Measure.map` is defined for arbitrary maps.) -/
lemma map_eq_self_of_forall_mem_eq {α : Type*} [MeasurableSpace α] {ρ : Measure α} {s : Set α}
    (hs : ρ sᶜ = 0) {f : α → α} (hf : ∀ x ∈ s, f x = x) : ρ.map f = ρ := by
  have hae : f =ᵐ[ρ] id := by
    filter_upwards [(mem_ae_iff (μ := ρ) (s := s)).mpr hs] with x hx
    exact hf x hx
  rw [Measure.map_congr hae, Measure.map_id]

/-- Conjugation by an element `g₀` that commutes with every element of a subgroup `T` fixes every
measure carried by `T`. -/
lemma map_conj_eq_of_carried_of_comm {T : Subgroup SL3} {g₀ : SL3}
    (hcent : ∀ g ∈ T, g₀ * g = g * g₀) {ρ : Measure SL3} (hρ : ρ (T : Set SL3)ᶜ = 0) :
    ρ.map (fun g => g₀ * g * g₀⁻¹) = ρ :=
  map_eq_self_of_forall_mem_eq hρ fun g hg => by
    rw [hcent g hg, mul_assoc, mul_inv_cancel, mul_one]

/-- Powers of an element that commutes with `b` commute with `b`. -/
lemma pow_mul_eq_mul_pow {G : Type*} [Group G] {a b : G} (h : a * b = b * a) (n : ℕ) :
    a ^ n * b = b * a ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    calc a ^ (k + 1) * b = (a ^ k * a) * b := by rw [pow_succ]
      _ = a ^ k * (a * b) := by rw [mul_assoc]
      _ = a ^ k * (b * a) := by rw [h]
      _ = (a ^ k * b) * a := by rw [mul_assoc]
      _ = (b * a ^ k) * a := by rw [ih]
      _ = b * (a ^ k * a) := by rw [mul_assoc]
      _ = b * a ^ (k + 1) := by rw [pow_succ]

/-! ## The single-step covariance -/

/-- **Exact invariance of `νT` under a single diagonal step.**  If `aDiag t` centralises the
horospherical subgroup `T`, then the `T`-leafwise measures are a.e. invariant under `aDiag t`. -/
theorem ae_aDiag_smul_eq (hLeaf : P_Leafwise) {μ : Measure X3} [IsProbabilityMeasure μ]
    (hμ : IsAInvariant μ) {T : Subgroup SL3} (hT : IsHoro T)
    {νT : X3 → Measure SL3} {XT : Set X3} (hνT : IsLeafwise μ T νT XT)
    (t : Fin 3 → ℝ) (hcent : ∀ g ∈ T, aDiag t * g = g * aDiag t) :
    ∀ᵐ x ∂μ, νT (aDiag t • x) = νT x := by
  -- (U7) is available for `νT`, thanks to `P_Leafwise`; a contracting direction exists since
  -- `T` is horospherical, and `μ` is `A`-invariant.
  obtain ⟨t0, ht0⟩ := hT.2.2
  have hmp : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ := hμ t0
  have hU := (hLeaf μ T hT t0 hmp ht0).2 νT XT hνT
  obtain ⟨-, -, -, -, -, -, hU7, -, -⟩ := hU
  obtain ⟨X'', hX''sub, hX''meas, hX''conull, hX''cov⟩ := hU7 hμ
  -- `X''` and its preimage under `x ↦ aDiag t • x` are both conull.
  have h1 : ∀ᵐ x ∂μ, x ∈ X'' := (mem_ae_iff (μ := μ) (s := X'')).mpr hX''conull
  have h2 : ∀ᵐ x ∂μ, aDiag t • x ∈ X'' := by
    have h0 : μ ((fun x : X3 => aDiag t • x) ⁻¹' X''ᶜ) = 0 := by
      rw [← Measure.map_apply (hμ t).measurable hX''meas.compl, (hμ t).map_eq]
      exact hX''conull
    rw [ae_iff]
    have hset : {a : X3 | ¬ aDiag t • a ∈ X''} = (fun x : X3 => aDiag t • x) ⁻¹' X''ᶜ := by
      ext a; simp
    rw [hset]
    exact h0
  filter_upwards [h1, h2] with x hx1 hx2
  obtain ⟨c, -, -, hceq⟩ := hX''cov t x hx1 hx2
  have hxXT : x ∈ XT := hX''sub hx1
  have hx2XT : aDiag t • x ∈ XT := hX''sub hx2
  -- The conjugating map is the identity on the carrier `T` of `νT x`.
  have hconj := map_conj_eq_of_carried_of_comm hcent (hνT.carried x hxXT)
  -- Evaluate the proportionality `νT (a • x) = c • νT x` on `Box1 T`, where both sides equal `1`.
  have h3 : νT (aDiag t • x) (Box1 T) = c * νT x (Box1 T) := by
    rw [hceq, Measure.smul_apply, hconj, smul_eq_mul]
  rw [hνT.normalised (aDiag t • x) hx2XT, hνT.normalised x hxXT, mul_one] at h3
  calc νT (aDiag t • x) = c • (νT x).map (fun g => aDiag t * g * (aDiag t)⁻¹) := hceq
    _ = c • νT x := by rw [hconj]
    _ = νT x := by rw [h3.symm, one_smul]

/-! ## The requested statement -/

theorem nuT_aDiag_pow_invariant (hLeaf : Work.EKLContract.P_Leafwise) {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ] (hμ : Work.EKLContract.IsAInvariant μ) {T : Subgroup Work.EKLContract.SL3} (hT : Work.EKLContract.IsHoro T) {νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XT : Set Work.EKLContract.X3} (hνT : Work.EKLContract.IsLeafwise μ T νT XT) (t : Fin 3 → ℝ) (hcent : ∀ g ∈ T, Work.EKLContract.aDiag t * g = g * Work.EKLContract.aDiag t) (n : ℕ) :
    ∀ᵐ x ∂μ, νT (Work.EKLContract.aDiag t ^ n • x) = νT x := by
  -- `aDiag (n • t) = aDiag t ^ n` still centralises `T`.
  have hcent' : ∀ g ∈ T, aDiag (n • t) * g = g * aDiag (n • t) := by
    intro g hg
    rw [aDiag_nsmul]
    exact pow_mul_eq_mul_pow (hcent g hg) n
  have h := ae_aDiag_smul_eq hLeaf hμ hT hνT (n • t) hcent'
  rw [aDiag_nsmul] at h
  exact h

end Work.EKLProd
