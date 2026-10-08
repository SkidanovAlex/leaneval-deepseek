import Mathlib
import Submission.Work.Hering.GL32.AppIXSurj
import Submission.Work.Hering.GL32.AppIXTheta

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix IX: the common kernel `K₄` of the four maps

`K₄ = ker combinedMap = ker aug ∩ ker phi ∩ ker psi ∩ ker theta` is a `GL(3,2)`-submodule of the
permutation module `W = k[Ω]`, of dimension `21 - 15 = 6` (because `combinedMap` is onto, see
`combined_surjective`).  We show that it is the sum of the two transposed maps

`K₄ = phiStar.range ⊔ psiStar.range`.

The inclusion `⊇` consists of the eight explicit vanishings `aug ∘ phiStar = 0`, ... ,
`theta ∘ psiStar = 0`; the converse follows from `dim K₄ = 6`, the injectivity of `phiStar` and
`psiStar`, and `phiStar.range ⊓ psiStar.range = ⊥`.  Injectivity and disjointness are proved with
the pairing identity `aug (w * phiStar s) = s (phi w)` (and its analogue for `psiStar`), which
turns the explicit elements `psi_lift_fᵢ ∈ ker aug ∩ ker phi` into test functionals.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.Hering.GL32

/-! ## Closed forms for the generators -/

lemma phiStar_f₀ : (phiStar f₀ : W) = fun p => psum p 0 := by
  funext p; rw [phiStar_apply, f₀, LinearMap.proj_apply]

lemma phiStar_f₁ : (phiStar f₁ : W) = fun p => psum p 1 := by
  funext p; rw [phiStar_apply, f₁, LinearMap.proj_apply]

lemma phiStar_f₂ : (phiStar f₂ : W) = fun p => psum p 2 := by
  funext p; rw [phiStar_apply, f₂, LinearMap.proj_apply]

lemma psiStar_e₀ : (psiStar e₀ : W) = fun p => (pdF p) e₀ := by
  funext p; rw [psiStar_apply]

lemma psiStar_e₁ : (psiStar e₁ : W) = fun p => (pdF p) e₁ := by
  funext p; rw [psiStar_apply]

lemma psiStar_e₂ : (psiStar e₂ : W) = fun p => (pdF p) e₂ := by
  funext p; rw [psiStar_apply]

/-! ## Vanishing of the eight composites -/

lemma comp_eq_zero_of_basis {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (F : Module.Dual (ZMod 2) F2v →ₗ[ZMod 2] M) (h₀ : F f₀ = 0) (h₁ : F f₁ = 0)
    (h₂ : F f₂ = 0) : F = 0 := by
  apply LinearMap.ext
  intro s
  conv_lhs => rw [show s = s e₀ • f₀ + s e₁ • f₁ + s e₂ • f₂ from (eq_sum_smul_f s).symm]
  simp only [map_add, map_smul, LinearMap.zero_apply, h₀, h₁, h₂, smul_zero, add_zero]

lemma comp_eq_zero_of_basis_V {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (F : F2v →ₗ[ZMod 2] M) (h₀ : F e₀ = 0) (h₁ : F e₁ = 0) (h₂ : F e₂ = 0) : F = 0 := by
  apply LinearMap.ext
  intro v
  conv_lhs => rw [← eq_sum_smul_e v]
  simp only [map_add, map_smul, LinearMap.zero_apply, h₀, h₁, h₂, smul_zero, add_zero]

lemma aug_comp_phiStar : aug.comp phiStar = 0 :=
  comp_eq_zero_of_basis _
    (by show aug (phiStar f₀) = 0; rw [phiStar_f₀]; decide)
    (by show aug (phiStar f₁) = 0; rw [phiStar_f₁]; decide)
    (by show aug (phiStar f₂) = 0; rw [phiStar_f₂]; decide)

lemma phi_comp_phiStar : phi.comp phiStar = 0 :=
  comp_eq_zero_of_basis _
    (by show phi (phiStar f₀) = 0; rw [phiStar_f₀]; decide)
    (by show phi (phiStar f₁) = 0; rw [phiStar_f₁]; decide)
    (by show phi (phiStar f₂) = 0; rw [phiStar_f₂]; decide)

lemma psi_comp_phiStar : psi.comp phiStar = 0 :=
  comp_eq_zero_of_basis _
    (by show psi (phiStar f₀) = 0; rw [phiStar_f₀]; decide)
    (by show psi (phiStar f₁) = 0; rw [phiStar_f₁]; decide)
    (by show psi (phiStar f₂) = 0; rw [phiStar_f₂]; decide)

lemma theta_comp_phiStar : theta.comp phiStar = 0 :=
  comp_eq_zero_of_basis _
    (by show theta (phiStar f₀) = 0; rw [phiStar_f₀]; decide)
    (by show theta (phiStar f₁) = 0; rw [phiStar_f₁]; decide)
    (by show theta (phiStar f₂) = 0; rw [phiStar_f₂]; decide)

lemma aug_comp_psiStar : aug.comp psiStar = 0 :=
  comp_eq_zero_of_basis_V _
    (by show aug (psiStar e₀) = 0; rw [psiStar_e₀]; decide)
    (by show aug (psiStar e₁) = 0; rw [psiStar_e₁]; decide)
    (by show aug (psiStar e₂) = 0; rw [psiStar_e₂]; decide)

lemma phi_comp_psiStar : phi.comp psiStar = 0 :=
  comp_eq_zero_of_basis_V _
    (by show phi (psiStar e₀) = 0; rw [psiStar_e₀]; decide)
    (by show phi (psiStar e₁) = 0; rw [psiStar_e₁]; decide)
    (by show phi (psiStar e₂) = 0; rw [psiStar_e₂]; decide)

lemma psi_comp_psiStar : psi.comp psiStar = 0 :=
  comp_eq_zero_of_basis_V _
    (by show psi (psiStar e₀) = 0; rw [psiStar_e₀]; decide)
    (by show psi (psiStar e₁) = 0; rw [psiStar_e₁]; decide)
    (by show psi (psiStar e₂) = 0; rw [psiStar_e₂]; decide)

lemma theta_comp_psiStar : theta.comp psiStar = 0 :=
  comp_eq_zero_of_basis_V _
    (by show theta (psiStar e₀) = 0; rw [psiStar_e₀]; decide)
    (by show theta (psiStar e₁) = 0; rw [psiStar_e₁]; decide)
    (by show theta (psiStar e₂) = 0; rw [psiStar_e₂]; decide)

lemma mem_K4_iff (f : W) : f ∈ K4 ↔ aug f = 0 ∧ phi f = 0 ∧ psi f = 0 ∧ theta f = 0 := by
  show f ∈ LinearMap.ker combinedMap ↔ _
  rw [LinearMap.mem_ker]
  show (aug f, phi f, psi f, theta f) = (0, 0, 0, 0) ↔ _
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg (fun x => x.2.1) h, congrArg (fun x => x.2.2.1) h,
      congrArg (fun x => x.2.2.2) h⟩
  · rintro ⟨h1, h2, h3, h4⟩
    simp only [h1, h2, h3, h4]

lemma phiStar_range_le_K4 : phiStar.range ≤ K4 := by
  rintro f ⟨s, rfl⟩
  rw [mem_K4_iff]
  exact ⟨LinearMap.congr_fun aug_comp_phiStar s, LinearMap.congr_fun phi_comp_phiStar s,
    LinearMap.congr_fun psi_comp_phiStar s, LinearMap.congr_fun theta_comp_phiStar s⟩

lemma psiStar_range_le_K4 : psiStar.range ≤ K4 := by
  rintro f ⟨v, rfl⟩
  rw [mem_K4_iff]
  exact ⟨LinearMap.congr_fun aug_comp_psiStar v, LinearMap.congr_fun phi_comp_psiStar v,
    LinearMap.congr_fun psi_comp_psiStar v, LinearMap.congr_fun theta_comp_psiStar v⟩

/-! ## The two pairing identities -/

lemma aug_mul_phiStar (w : W) (s : Module.Dual (ZMod 2) F2v) :
    aug (w * phiStar s) = s (phi w) := by
  show (∑ p : Pair, (w * phiStar s) p) = s (∑ p : Pair, w p • psum p)
  rw [map_sum]
  exact Finset.sum_congr rfl (fun p _ => by rw [Pi.mul_apply, phiStar_apply, map_smul, smul_eq_mul])

lemma aug_mul_psiStar (w : W) (v : F2v) : aug (w * psiStar v) = (psi w) v := by
  show (∑ p : Pair, (w * psiStar v) p) = (∑ p : Pair, w p • pdF p) v
  rw [LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun p _ => by rw [Pi.mul_apply, psiStar_apply, LinearMap.smul_apply, smul_eq_mul])

lemma exists_coord_eq_one (v : F2v) (hv : v ≠ 0) : v 0 = 1 ∨ v 1 = 1 ∨ v 2 = 1 := by
  revert hv; revert v; decide

lemma phiStar_injective : Function.Injective phiStar := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro s hs
  have h0 : phiStar s = 0 := hs
  apply LinearMap.ext
  intro v
  obtain ⟨w, -, hw⟩ := phi_ker_aug_surj v
  have h1 : aug (w * phiStar s) = s (phi w) := aug_mul_phiStar w s
  rw [h0, mul_zero, map_zero] at h1
  rw [← hw, ← h1]
  simp

lemma psiStar_injective : Function.Injective psiStar := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  have h0 : psiStar v = 0 := hv
  by_contra hv0
  obtain h | h | h := exists_coord_eq_one v hv0
  · obtain ⟨u, -, -, hu⟩ := psi_lift_f₀
    have h2 : (psi u) v = 1 := by rw [hu, f₀, LinearMap.proj_apply, h]
    rw [← aug_mul_psiStar u v, h0, mul_zero, map_zero] at h2
    exact zero_ne_one h2
  · obtain ⟨u, -, -, hu⟩ := psi_lift_f₁
    have h2 : (psi u) v = 1 := by rw [hu, f₁, LinearMap.proj_apply, h]
    rw [← aug_mul_psiStar u v, h0, mul_zero, map_zero] at h2
    exact zero_ne_one h2
  · obtain ⟨u, -, -, hu⟩ := psi_lift_f₂
    have h2 : (psi u) v = 1 := by rw [hu, f₂, LinearMap.proj_apply, h]
    rw [← aug_mul_psiStar u v, h0, mul_zero, map_zero] at h2
    exact zero_ne_one h2

lemma disjoint_ranges : phiStar.range ⊓ psiStar.range = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro f ⟨hf₁, hf₂⟩
  obtain ⟨s, hs⟩ := hf₁
  obtain ⟨v, hv⟩ := hf₂
  by_cases hv0 : v = 0
  · rw [← hv, hv0, map_zero]
  · obtain h | h | h := exists_coord_eq_one v hv0
    · obtain ⟨u, -, hu1, hu2⟩ := psi_lift_f₀
      have hA : aug (u * psiStar v) = 0 := by rw [hv, ← hs, aug_mul_phiStar, hu1, map_zero]
      have hB : (psi u) v = 1 := by rw [hu2, f₀, LinearMap.proj_apply, h]
      rw [← aug_mul_psiStar u v, hA] at hB
      exact (zero_ne_one hB).elim
    · obtain ⟨u, -, hu1, hu2⟩ := psi_lift_f₁
      have hA : aug (u * psiStar v) = 0 := by rw [hv, ← hs, aug_mul_phiStar, hu1, map_zero]
      have hB : (psi u) v = 1 := by rw [hu2, f₁, LinearMap.proj_apply, h]
      rw [← aug_mul_psiStar u v, hA] at hB
      exact (zero_ne_one hB).elim
    · obtain ⟨u, -, hu1, hu2⟩ := psi_lift_f₂
      have hA : aug (u * psiStar v) = 0 := by rw [hv, ← hs, aug_mul_phiStar, hu1, map_zero]
      have hB : (psi u) v = 1 := by rw [hu2, f₂, LinearMap.proj_apply, h]
      rw [← aug_mul_psiStar u v, hA] at hB
      exact (zero_ne_one hB).elim

/-! ## Dimensions -/

lemma finrank_W : Module.finrank (ZMod 2) W = 21 := by
  rw [Module.finrank_fintype_fun_eq_card]
  decide

lemma finrank_F2v : Module.finrank (ZMod 2) F2v = 3 := by
  rw [Module.finrank_fintype_fun_eq_card]
  decide

lemma finrank_dual : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) F2v) = 3 := by
  rw [Subspace.dual_finrank_eq, Module.finrank_fintype_fun_eq_card]
  decide

lemma finrank_Mat3 : Module.finrank (ZMod 2) Mat3 = 9 := by
  rw [Module.finrank_matrix]
  simp

lemma finrank_M4 : Module.finrank (ZMod 2) M4 = 8 := by
  change Module.finrank (ZMod 2) ↥(LinearMap.ker traceLin) = 8
  have h1 : traceLin (Matrix.of ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]]) = 1 := by decide
  have htop : LinearMap.range traceLin = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    rcases (show x = 0 ∨ x = 1 by revert x; decide) with h | h
    · rw [h]; exact Submodule.zero_mem _
    · rw [h, ← h1]; exact ⟨_, rfl⟩
  have h := LinearMap.finrank_range_add_finrank_ker (f := traceLin)
  rw [htop, finrank_top, Module.finrank_self, finrank_Mat3] at h
  omega

lemma finrank_target :
    Module.finrank (ZMod 2) (ZMod 2 × F2v × Module.Dual (ZMod 2) F2v × M4) = 15 := by
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod]
  rw [Module.finrank_self, finrank_F2v, finrank_dual, finrank_M4]

lemma finrank_K4 : Module.finrank (ZMod 2) K4 = 6 := by
  have h := LinearMap.finrank_range_add_finrank_ker (f := combinedMap)
  rw [show LinearMap.ker combinedMap = K4 from rfl, LinearMap.range_eq_top.mpr combined_surjective,
    finrank_top, finrank_target, finrank_W] at h
  omega

lemma finrank_range_phiStar : Module.finrank (ZMod 2) phiStar.range = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker (f := phiStar)
  rw [show LinearMap.ker phiStar = ⊥ from LinearMap.ker_eq_bot.mpr phiStar_injective,
    finrank_bot, add_zero, finrank_dual] at h
  exact h

lemma finrank_range_psiStar : Module.finrank (ZMod 2) psiStar.range = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker (f := psiStar)
  rw [show LinearMap.ker psiStar = ⊥ from LinearMap.ker_eq_bot.mpr psiStar_injective,
    finrank_bot, add_zero, finrank_F2v] at h
  exact h

/-- **`K₄` is the sum of the two three-dimensional ranges.** -/
theorem K4_eq_sup : K4 = phiStar.range ⊔ psiStar.range := by
  have hle : phiStar.range ⊔ psiStar.range ≤ K4 := sup_le phiStar_range_le_K4 psiStar_range_le_K4
  have hrank : Module.finrank (ZMod 2) ↥(phiStar.range ⊔ psiStar.range) = 6 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq phiStar.range psiStar.range
    rw [disjoint_ranges, finrank_bot, add_zero, finrank_range_phiStar,
      finrank_range_psiStar] at h
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hrank, finrank_K4])).symm

end Work.Hering.GL32
