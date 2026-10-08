import Mathlib
import Submission.Work.HallHigman.GLCore.FourierSetup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman.GLCore

open Finset

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [Nontrivial V]
variable {E : Type*} [Group E] [Fintype E]

omit [Fintype E] in
/-- A central `f` makes the character `e ↦ λ([e,f])` trivial. -/
theorem commChar_eq_one_of_mem_center (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    (hcomm : ∀ e f : E, e * f * e⁻¹ * f⁻¹ ∈ Subgroup.center E)
    {f : E} (hf : f ∈ Subgroup.center E) (e : E) :
    commChar σ hsc hcomm f e = 1 := by
  have hfe : e * f * e⁻¹ * f⁻¹ = 1 := by
    rw [conj_eq_of_mem_center hf e, mul_inv_cancel]
  have h1 : (⟨e * f * e⁻¹ * f⁻¹, hcomm e f⟩ : Subgroup.center E) = 1 :=
    Subtype.ext (by simpa using hfe)
  rw [commChar_apply, h1, map_one]
  rfl

/-- For central `f` the character sum `Σ_e λ([e,f])` equals the order of `E`. -/
theorem sum_commChar_eq_card (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    (hcomm : ∀ e f : E, e * f * e⁻¹ * f⁻¹ ∈ Subgroup.center E)
    {f : E} (hf : f ∈ Subgroup.center E) :
    ∑ e : E, commChar σ hsc hcomm f e = (Nat.card E : K) := by
  rw [Finset.sum_congr rfl (fun e _ => commChar_eq_one_of_mem_center σ hsc hcomm hf e)]
  rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  simp

omit [Nontrivial V] [Fintype E] in
/-- A central element conjugates every endomorphism trivially. -/
theorem center_mul_conj (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    {f : E} (hf : f ∈ Subgroup.center E) (X : Module.End K V) :
    σ f * X * σ (f⁻¹) = X := by
  obtain ⟨c, hc⟩ := hsc f hf
  have h1 : (σ f : Module.End K V) = c • (1 : Module.End K V) := by
    rw [hc, Algebra.algebraMap_eq_smul_one]
  have hcomm : σ f * X = X * σ f := by
    rw [h1, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  calc σ f * X * σ (f⁻¹) = X * σ f * σ (f⁻¹) := by rw [hcomm]
    _ = X * (σ f * σ (f⁻¹)) := by rw [mul_assoc]
    _ = X * σ (f * f⁻¹) := by rw [map_mul]
    _ = X * σ 1 := by rw [mul_inv_cancel]
    _ = X * 1 := by rw [map_one]
    _ = X := mul_one X

/-- **Master identity of the Fourier lemma** (Step 4c of `NOTES_LEAD_ft_hallhigman.md` §2.2).
With `P = Work.HallHigman.GLCore.fourierP σ`, the projector `Y ↦ |E|⁻¹ Σ_{f} σ f · Y · σ f⁻¹`
onto the commutant `End_E(V)` (`Work.HallHigman.commutantOf σ`), one has
`Σ_{e ∈ E} σ e · P(σ(e⁻¹) · X) = |Z(E)| · X` for every `X : End_K V`.

The available ingredients (in `HallHigman/GLCore/FourierSetup`) are `fourierP_apply`,
`fourierP_smul_center` (`P(σ z · X) = σ z · P X` for `z ∈ Z(E)`), and the two character facts
`conj_sum_eq` (`Σ_e σ(e f e⁻¹) = (Σ_e λ([e,f])) • σ f`) and `sum_commChar_eq_zero`
(`Σ_e λ([e,f]) = 0` for `f ∉ Z(E)`). -/
theorem fourier_master_identity {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [Nontrivial V] {E : Type*} [Group E] [Fintype E] [Fintype (E ⧸ Subgroup.center E)]
    (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    (hfaith : ∀ z ∈ Subgroup.center E, σ z = 1 → z = 1)
    (hcomm : ∀ e f : E, e * f * e⁻¹ * f⁻¹ ∈ Subgroup.center E)
    (hE : (Nat.card E : K) ≠ 0) (X : Module.End K V) :
    ∑ e : E, σ e * Work.HallHigman.GLCore.fourierP σ (σ (e⁻¹) * X)
      = (Nat.card (Subgroup.center E) : K) • X := by
  classical
  -- Each summand expands as `|E|⁻¹ • Σ_f σ(e f e⁻¹) X σ(f⁻¹)`.
  have hterm : ∀ e : E, σ e * fourierP σ (σ (e⁻¹) * X)
      = (Nat.card E : K)⁻¹ • ∑ f : E, σ (e * f * e⁻¹) * X * σ (f⁻¹) := by
    intro e
    rw [fourierP_apply, mul_smul_comm, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro f _
    simp only [map_mul]
    noncomm_ring
  -- Swapping the two summations and applying `conj_sum_eq` leaves the character sum as a weight.
  have hL : ∑ e : E, σ e * fourierP σ (σ (e⁻¹) * X)
      = (Nat.card E : K)⁻¹ •
        ∑ f : E, (∑ e : E, commChar σ hsc hcomm f e) • (σ f * X * σ (f⁻¹)) := by
    rw [Finset.sum_congr rfl (fun e _ => hterm e)]
    rw [← Finset.smul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro f _
    rw [← Finset.sum_mul, ← Finset.sum_mul, conj_sum_eq, smul_mul_assoc, smul_mul_assoc]
  -- Only the central `f` contribute, each with weight `|E|` and trivial conjugation.
  have hC : ∑ f : E, (∑ e : E, commChar σ hsc hcomm f e) • (σ f * X * σ (f⁻¹))
      = (Nat.card (Subgroup.center E) : K) • ((Nat.card E : K) • X) := by
    have hcard : (Finset.univ.filter (fun f : E => f ∈ Subgroup.center E)).card
        = Nat.card (Subgroup.center E) := by
      rw [← Fintype.card_subtype (p := fun f : E => f ∈ Subgroup.center E)]
      rw [Nat.card_eq_fintype_card]
    have hstep1 : ∑ f : E, (∑ e : E, commChar σ hsc hcomm f e) • (σ f * X * σ (f⁻¹))
        = ∑ f ∈ Finset.univ.filter (fun f : E => f ∈ Subgroup.center E),
            (∑ e : E, commChar σ hsc hcomm f e) • (σ f * X * σ (f⁻¹)) := by
      refine (Finset.sum_subset (s₁ := Finset.univ.filter (fun f : E => f ∈ Subgroup.center E))
        (s₂ := Finset.univ) (Finset.filter_subset _ _) ?_).symm
      intro x _ hx1
      rw [Finset.mem_filter] at hx1
      simp only [Finset.mem_univ, true_and] at hx1
      rw [sum_commChar_eq_zero σ hsc hfaith hcomm hx1, zero_smul]
    have hstep2 : ∑ f ∈ Finset.univ.filter (fun f : E => f ∈ Subgroup.center E),
            (∑ e : E, commChar σ hsc hcomm f e) • (σ f * X * σ (f⁻¹))
        = (Nat.card (Subgroup.center E) : K) • ((Nat.card E : K) • X) := by
      have hpoint : ∀ f ∈ Finset.univ.filter (fun f : E => f ∈ Subgroup.center E),
          (∑ e : E, commChar σ hsc hcomm f e) • (σ f * X * σ (f⁻¹))
            = (Nat.card E : K) • X := by
        intro f hf
        rw [Finset.mem_filter] at hf
        rw [sum_commChar_eq_card σ hsc hcomm hf.2, center_mul_conj σ hsc hf.2 X]
      rw [Finset.sum_congr rfl hpoint, Finset.sum_const, hcard]
      rw [Nat.cast_smul_eq_nsmul K (Nat.card (Subgroup.center E)) ((Nat.card E : K) • X)]
    rw [hstep1, hstep2]
  rw [hL, hC, smul_smul, smul_smul]
  congr 1
  rw [mul_assoc, mul_comm (Nat.card (Subgroup.center E) : K) (Nat.card E : K), ← mul_assoc,
    inv_mul_cancel₀ hE, one_mul]

end Work.HallHigman.GLCore
