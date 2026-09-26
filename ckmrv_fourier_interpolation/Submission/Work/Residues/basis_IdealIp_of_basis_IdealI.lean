import Mathlib
import Submission.Work.Residues.Basic

namespace Work.Residues

open Work.Kernels

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Finite linear combinations -/

/-- The linear map `c ↦ ∑ i, c i • v i` attached to a finite family `v`. -/
def finsumLinComb {ι M : Type*} [Fintype ι] [AddCommMonoid M] [Module ℂ M] (v : ι → M) :
    (ι → ℂ) →ₗ[ℂ] M where
  toFun c := ∑ i, c i • v i
  map_add' c d := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.smul_apply, smul_smul]
    simp

lemma finsumLinComb_apply {ι M : Type*} [Fintype ι] [AddCommMonoid M] [Module ℂ M]
    (v : ι → M) (c : ι → ℂ) : finsumLinComb v c = ∑ i, c i • v i := rfl

lemma finsumLinComb_surjective {ι M : Type*} [Fintype ι] [AddCommMonoid M] [Module ℂ M]
    (v : ι → M) (h : Submodule.span ℂ (Set.range v) = ⊤) :
    Function.Surjective (finsumLinComb v) := by
  intro y
  have hy : y ∈ Submodule.span ℂ (Set.range v) := by rw [h]; trivial
  rw [Submodule.mem_span_range_iff_exists_fun ℂ] at hy
  obtain ⟨c, hc⟩ := hy
  exact ⟨c, hc⟩

/-! ## Elementary manipulations in a quotient -/

lemma mkQ_eq_neg_of_add_mem (p : Submodule ℂ R) {a b : R} (h : a + b ∈ p) :
    Submodule.mkQ p a = -Submodule.mkQ p b := by
  have h0 : Submodule.mkQ p (a + b) = 0 := (Submodule.Quotient.mk_eq_zero p).mpr h
  rw [map_add] at h0
  exact eq_neg_of_add_eq_zero_left h0

lemma mkQ_eq_of_sub_mem (p : Submodule ℂ R) {a b : R} (h : a - b ∈ p) :
    Submodule.mkQ p a = Submodule.mkQ p b := by
  have h0 : Submodule.mkQ p (a - b) = 0 := (Submodule.Quotient.mk_eq_zero p).mpr h
  rw [map_sub, sub_eq_zero] at h0
  exact h0

/-! ## The generators `1 + S`, `(1+S)T`, `(1+S)TS` of `𝓘_+` -/

lemma R_S_add_one_mem_idealIp : (R_S + 1 : R) ∈ idealIp := by
  have h1 : (R_S + 1) * R_S ∈ Work.Kernels.IdealIp :=
    Work.Kernels.mem_span2.mpr ⟨R_S, 0, by rw [mul_zero, add_zero]⟩
  have h3 : (R_S + 1) * R_S - (Rneg - 1) = (R_S + 1 : R) := by
    rw [add_mul, one_mul, R_S_mul_R_S_eq]
    noncomm_ring
  rw [← h3]
  exact Submodule.sub_mem _ (IdealIp_le_idealIp h1)
    (augIdeal_le_idealIp Rneg_sub_one_mem_augIdeal)

lemma M6_four_add_one_mem_idealIp : (M6 4 + M6 1 : R) ∈ idealIp := by
  have h : (R_S + 1) * R_T ∈ Work.Kernels.IdealIp :=
    Work.Kernels.mem_span2.mpr ⟨R_T, 0, by rw [mul_zero, add_zero]⟩
  have e : (R_S + 1) * R_T = (M6 4 + M6 1 : R) := by
    rw [M6_four, M6_one, add_mul, one_mul]
  rw [← e]; exact IdealIp_le_idealIp h

lemma M6_five_add_two_mem_idealIp : (M6 5 + M6 2 : R) ∈ idealIp := by
  have h : (R_S + 1) * (R_T * R_S) ∈ Work.Kernels.IdealIp :=
    Work.Kernels.mem_span2.mpr ⟨R_T * R_S, 0, by rw [mul_zero, add_zero]⟩
  have e : (R_S + 1) * (R_T * R_S) = (M6 5 + M6 2 : R) := by
    rw [M6_five, M6_two]
    noncomm_ring
  rw [← e]; exact IdealIp_le_idealIp h

/-! ## The generators `S - 1`, `(S-1)T`, `(S-1)TS` of `𝓘_-` -/

lemma R_S_sub_one_mem_idealIm : (R_S - 1 : R) ∈ idealIm := by
  have h : (R_S - 1) * 1 ∈ Work.Kernels.IdealIm :=
    Work.Kernels.mem_span2.mpr ⟨1, 0, by rw [mul_zero, add_zero]⟩
  simpa using IdealIm_le_idealIm h

lemma M6_four_sub_one_mem_idealIm : (M6 4 - M6 1 : R) ∈ idealIm := by
  have h : (R_S - 1) * R_T ∈ Work.Kernels.IdealIm :=
    Work.Kernels.mem_span2.mpr ⟨R_T, 0, by rw [mul_zero, add_zero]⟩
  have e : (R_S - 1) * R_T = (M6 4 - M6 1 : R) := by
    rw [M6_four, M6_one, sub_mul, one_mul]
  rw [← e]; exact IdealIm_le_idealIm h

lemma M6_five_sub_two_mem_idealIm : (M6 5 - M6 2 : R) ∈ idealIm := by
  have h : (R_S - 1) * (R_T * R_S) ∈ Work.Kernels.IdealIm :=
    Work.Kernels.mem_span2.mpr ⟨R_T * R_S, 0, by rw [mul_zero, add_zero]⟩
  have e : (R_S - 1) * (R_T * R_S) = (M6 5 - M6 2 : R) := by
    rw [M6_five, M6_two]
    noncomm_ring
  rw [← e]; exact IdealIm_le_idealIm h

/-! ## The images of `M3` in the two quotients -/

/-- The images of `1, T, TS` in `R ⧸ 𝓘_+`. -/
def vp : Fin 3 → (R ⧸ idealIp) := fun i => Submodule.mkQ idealIp (M3 i)

/-- The images of `1, T, TS` in `R ⧸ 𝓘_-`. -/
def vm : Fin 3 → (R ⧸ idealIm) := fun i => Submodule.mkQ idealIm (M3 i)

lemma mkQ_Ip_M6_mem (i : Fin 6) :
    Submodule.mkQ idealIp (M6 i) ∈ Submodule.span ℂ (Set.range vp) := by
  fin_cases i
  · change Submodule.mkQ idealIp (M6 0) ∈ Submodule.span ℂ (Set.range vp)
    have h : Submodule.mkQ idealIp (M6 0) = vp 0 := by
      change Submodule.mkQ idealIp (M6 0) = Submodule.mkQ idealIp (M3 0)
      rw [M6_zero, M3_zero]
    rw [h]; exact Submodule.subset_span ⟨0, rfl⟩
  · change Submodule.mkQ idealIp (M6 1) ∈ Submodule.span ℂ (Set.range vp)
    have h : Submodule.mkQ idealIp (M6 1) = vp 1 := by
      change Submodule.mkQ idealIp (M6 1) = Submodule.mkQ idealIp (M3 1)
      rw [M6_one, M3_one]
    rw [h]; exact Submodule.subset_span ⟨1, rfl⟩
  · change Submodule.mkQ idealIp (M6 2) ∈ Submodule.span ℂ (Set.range vp)
    have h : Submodule.mkQ idealIp (M6 2) = vp 2 := by
      change Submodule.mkQ idealIp (M6 2) = Submodule.mkQ idealIp (M3 2)
      rw [M6_two, M3_two]
    rw [h]; exact Submodule.subset_span ⟨2, rfl⟩
  · change Submodule.mkQ idealIp (M6 3) ∈ Submodule.span ℂ (Set.range vp)
    have h : Submodule.mkQ idealIp (M6 3) = - Submodule.mkQ idealIp (M6 0) :=
      mkQ_eq_neg_of_add_mem idealIp
        (by rw [M6_three, M6_zero]; exact R_S_add_one_mem_idealIp)
    have h2 : Submodule.mkQ idealIp (M6 0) = vp 0 := by
      change Submodule.mkQ idealIp (M6 0) = Submodule.mkQ idealIp (M3 0)
      rw [M6_zero, M3_zero]
    rw [h, h2]
    exact Submodule.neg_mem _ (Submodule.subset_span ⟨0, rfl⟩)
  · change Submodule.mkQ idealIp (M6 4) ∈ Submodule.span ℂ (Set.range vp)
    have h : Submodule.mkQ idealIp (M6 4) = - Submodule.mkQ idealIp (M6 1) :=
      mkQ_eq_neg_of_add_mem idealIp M6_four_add_one_mem_idealIp
    have h2 : Submodule.mkQ idealIp (M6 1) = vp 1 := by
      change Submodule.mkQ idealIp (M6 1) = Submodule.mkQ idealIp (M3 1)
      rw [M6_one, M3_one]
    rw [h, h2]
    exact Submodule.neg_mem _ (Submodule.subset_span ⟨1, rfl⟩)
  · change Submodule.mkQ idealIp (M6 5) ∈ Submodule.span ℂ (Set.range vp)
    have h : Submodule.mkQ idealIp (M6 5) = - Submodule.mkQ idealIp (M6 2) :=
      mkQ_eq_neg_of_add_mem idealIp M6_five_add_two_mem_idealIp
    have h2 : Submodule.mkQ idealIp (M6 2) = vp 2 := by
      change Submodule.mkQ idealIp (M6 2) = Submodule.mkQ idealIp (M3 2)
      rw [M6_two, M3_two]
    rw [h, h2]
    exact Submodule.neg_mem _ (Submodule.subset_span ⟨2, rfl⟩)

lemma mkQ_Im_M6_mem (i : Fin 6) :
    Submodule.mkQ idealIm (M6 i) ∈ Submodule.span ℂ (Set.range vm) := by
  fin_cases i
  · change Submodule.mkQ idealIm (M6 0) ∈ Submodule.span ℂ (Set.range vm)
    have h : Submodule.mkQ idealIm (M6 0) = vm 0 := by
      change Submodule.mkQ idealIm (M6 0) = Submodule.mkQ idealIm (M3 0)
      rw [M6_zero, M3_zero]
    rw [h]; exact Submodule.subset_span ⟨0, rfl⟩
  · change Submodule.mkQ idealIm (M6 1) ∈ Submodule.span ℂ (Set.range vm)
    have h : Submodule.mkQ idealIm (M6 1) = vm 1 := by
      change Submodule.mkQ idealIm (M6 1) = Submodule.mkQ idealIm (M3 1)
      rw [M6_one, M3_one]
    rw [h]; exact Submodule.subset_span ⟨1, rfl⟩
  · change Submodule.mkQ idealIm (M6 2) ∈ Submodule.span ℂ (Set.range vm)
    have h : Submodule.mkQ idealIm (M6 2) = vm 2 := by
      change Submodule.mkQ idealIm (M6 2) = Submodule.mkQ idealIm (M3 2)
      rw [M6_two, M3_two]
    rw [h]; exact Submodule.subset_span ⟨2, rfl⟩
  · change Submodule.mkQ idealIm (M6 3) ∈ Submodule.span ℂ (Set.range vm)
    have h : Submodule.mkQ idealIm (M6 3) = Submodule.mkQ idealIm (M6 0) :=
      mkQ_eq_of_sub_mem idealIm
        (by rw [M6_three, M6_zero]; exact R_S_sub_one_mem_idealIm)
    have h2 : Submodule.mkQ idealIm (M6 0) = vm 0 := by
      change Submodule.mkQ idealIm (M6 0) = Submodule.mkQ idealIm (M3 0)
      rw [M6_zero, M3_zero]
    rw [h, h2]
    exact Submodule.subset_span ⟨0, rfl⟩
  · change Submodule.mkQ idealIm (M6 4) ∈ Submodule.span ℂ (Set.range vm)
    have h : Submodule.mkQ idealIm (M6 4) = Submodule.mkQ idealIm (M6 1) :=
      mkQ_eq_of_sub_mem idealIm M6_four_sub_one_mem_idealIm
    have h2 : Submodule.mkQ idealIm (M6 1) = vm 1 := by
      change Submodule.mkQ idealIm (M6 1) = Submodule.mkQ idealIm (M3 1)
      rw [M6_one, M3_one]
    rw [h, h2]
    exact Submodule.subset_span ⟨1, rfl⟩
  · change Submodule.mkQ idealIm (M6 5) ∈ Submodule.span ℂ (Set.range vm)
    have h : Submodule.mkQ idealIm (M6 5) = Submodule.mkQ idealIm (M6 2) :=
      mkQ_eq_of_sub_mem idealIm M6_five_sub_two_mem_idealIm
    have h2 : Submodule.mkQ idealIm (M6 2) = vm 2 := by
      change Submodule.mkQ idealIm (M6 2) = Submodule.mkQ idealIm (M3 2)
      rw [M6_two, M3_two]
    rw [h, h2]
    exact Submodule.subset_span ⟨2, rfl⟩

/-- **Paper Proposition 3.8(2)** for the ideal `𝓘_+ = (S+I)R + (T-I)²R + (z-1)R`: assuming
part (1), that the images of `1, T, TS, S, ST, STS` are a basis of `R/𝓘`, the images of
`1, T, TS` are a basis of `R/𝓘_+`. -/
theorem basis_IdealIp_of_basis_IdealI
    (hI : ∃ b : Module.Basis (Fin 6) ℂ (Work.Kernels.R ⧸ Work.Residues.idealI),
      ∀ i, b i = Submodule.mkQ Work.Residues.idealI (Work.Residues.M6 i)) :
    ∃ b : Module.Basis (Fin 3) ℂ (Work.Kernels.R ⧸ Work.Residues.idealIp),
      ∀ i, b i = Submodule.mkQ Work.Residues.idealIp (Work.Residues.M3 i) := by
  obtain ⟨b, hb⟩ := hI
  -- Every element of `R ⧸ 𝓘` is reduced to the basis `M6` modulo `𝓘`, hence modulo `𝓘_±`.
  have reduce_repr : ∀ (p : Submodule ℂ R) (hIp : idealI ≤ p) (r : R),
      Submodule.mkQ p r =
        ∑ i : Fin 6, (b.repr (Submodule.mkQ idealI r)) i • Submodule.mkQ p (M6 i) := by
    intro p hIp r
    set c : Fin 6 →₀ ℂ := b.repr (Submodule.mkQ idealI r) with hc
    have hX : Submodule.mkQ idealI (∑ i, c i • M6 i) = Submodule.mkQ idealI r := by
      rw [map_sum]
      have hterm : ∀ i, Submodule.mkQ idealI (c i • M6 i) = c i • b i :=
        fun i => by rw [map_smul, ← hb i]
      rw [Finset.sum_congr rfl (fun i _ => hterm i)]
      simpa [hc] using Module.Basis.sum_repr b (Submodule.mkQ idealI r)
    have hmem : r - ∑ i, c i • M6 i ∈ idealI := by
      have key : Submodule.mkQ idealI (r - ∑ i, c i • M6 i) = 0 := by
        rw [map_sub, hX, sub_self]
      exact (Submodule.Quotient.mk_eq_zero idealI).mp key
    have hsub : Submodule.mkQ p (r - ∑ i, c i • M6 i) = 0 :=
      (Submodule.Quotient.mk_eq_zero p).mpr (hIp hmem)
    rw [map_sub, sub_eq_zero] at hsub
    rw [hsub, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
  -- The images of `M6` span `R ⧸ 𝓘_+`.
  have hspan_p : Submodule.span ℂ (Set.range vp) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective idealIp y
    rw [reduce_repr idealIp idealI_le_idealIp r]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    exact Submodule.smul_mem _ _ (mkQ_Ip_M6_mem i)
  -- The images of `M6` span `R ⧸ 𝓘_-`.
  have hspan_m : Submodule.span ℂ (Set.range vm) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective idealIm y
    rw [reduce_repr idealIm idealI_le_idealIm r]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    exact Submodule.smul_mem _ _ (mkQ_Im_M6_mem i)
  -- Finiteness and the dimension bounds `dim R/𝓘_± ≤ 3`.
  haveI hfin_p : Module.Finite ℂ (R ⧸ idealIp) :=
    Module.Finite.of_surjective (finsumLinComb vp) (finsumLinComb_surjective vp hspan_p)
  haveI hfin_m : Module.Finite ℂ (R ⧸ idealIm) :=
    Module.Finite.of_surjective (finsumLinComb vm) (finsumLinComb_surjective vm hspan_m)
  have hle_p : Module.finrank ℂ (R ⧸ idealIp) ≤ 3 := by
    have h := LinearMap.finrank_le_finrank_of_surjective (R := ℂ)
      (finsumLinComb_surjective vp hspan_p)
    rw [Module.finrank_fintype_fun_eq_card ℂ, Fintype.card_fin] at h
    exact h
  have hle_m : Module.finrank ℂ (R ⧸ idealIm) ≤ 3 := by
    have h := LinearMap.finrank_le_finrank_of_surjective (R := ℂ)
      (finsumLinComb_surjective vm hspan_m)
    rw [Module.finrank_fintype_fun_eq_card ℂ, Fintype.card_fin] at h
    exact h
  -- The diagonal map `R ⧸ 𝓘 → R ⧸ 𝓘_+ × R ⧸ 𝓘_-` is injective.
  let ψ : (R ⧸ idealI) →ₗ[ℂ] ((R ⧸ idealIp) × (R ⧸ idealIm)) :=
    Submodule.liftQ idealI (LinearMap.prod (Submodule.mkQ idealIp) (Submodule.mkQ idealIm)) (by
      intro x hx
      rw [LinearMap.mem_ker]
      refine Prod.ext ?_ ?_
      · exact (Submodule.Quotient.mk_eq_zero idealIp).mpr (idealI_le_idealIp hx)
      · exact (Submodule.Quotient.mk_eq_zero idealIm).mpr (idealI_le_idealIm hx))
  have hψ_inj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective idealI y
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply] at hy
    have hy' : (Submodule.mkQ idealIp r, Submodule.mkQ idealIm r) = (0, 0) := hy
    have h1 : Submodule.mkQ idealIp r = 0 := congrArg Prod.fst hy'
    have h2 : Submodule.mkQ idealIm r = 0 := congrArg Prod.snd hy'
    refine (Submodule.Quotient.mk_eq_zero idealI).mpr ?_
    rw [idealI_eq_idealIp_inf_idealIm]
    exact ⟨(Submodule.Quotient.mk_eq_zero idealIp).mp h1,
      (Submodule.Quotient.mk_eq_zero idealIm).mp h2⟩
  -- Dimensions: `6 = dim R/𝓘 ≤ dim R/𝓘_+ + dim R/𝓘_- ≤ 3 + 3`.
  have hfin_A : Module.finrank ℂ (R ⧸ idealI) = 6 := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hfin_P : Module.finrank ℂ (R ⧸ idealIp) = 3 := by
    have h := LinearMap.finrank_le_finrank_of_injective (R := ℂ) hψ_inj
    rw [hfin_A, Module.finrank_prod] at h
    omega
  -- Hence `v` is a basis of `R ⧸ 𝓘_+`.
  have hLI : LinearIndependent ℂ vp := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    change Fintype.card (Fin 3) = Module.finrank ℂ (↥(Submodule.span ℂ (Set.range vp)))
    rw [hspan_p, (Submodule.topEquiv (R := ℂ)).finrank_eq, hfin_P, Fintype.card_fin]
  have hsp : (⊤ : Submodule ℂ (R ⧸ idealIp)) ≤ Submodule.span ℂ (Set.range vp) := by
    rw [hspan_p]
  refine ⟨Module.Basis.mk hLI hsp, fun i => ?_⟩
  exact Module.Basis.mk_apply hLI hsp i

end

end Work.Residues
