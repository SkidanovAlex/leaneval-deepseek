import Mathlib
import Submission.Work.HP.MDEstimates.QuadAuxDefs
import Submission.Work.HP.MDEstimates.polarQuadFacts
import Submission.Work.HP.MDEstimates.hyperplaneFactor

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

noncomputable section

open MvPolynomial

namespace Work.HP.Q44Main.QuadCount

/-! ## The polar bilinear form of a homogeneous quadratic form

For `Q : MvPolynomial (Fin 5) ℚ` homogeneous of degree `2`, the polar form
`polQ Q x y = (Q(x+y) - Q(x) - Q(y))/2` is symmetric bilinear with `polQ Q x x = Q x`
(`polarQuadFacts`).  We package it as a `LinearMap.BilinForm` and record the facts we need. -/

/-- The polar bilinear form of a homogeneous quadratic form, packaged as a bilinear form. -/
def polB (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2) :
    (Fin 5 → ℚ) →ₗ[ℚ] (Fin 5 → ℚ) →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (fun x y => Work.HP.MDEstimates.polQ Q x y)
    (fun x x' y => (Work.HP.MDEstimates.polarQuadFacts Q hQ).1 x x' y)
    (fun c x y => (Work.HP.MDEstimates.polarQuadFacts Q hQ).2.1 c x y)
    (fun x y y' => by
      rw [(Work.HP.MDEstimates.polarQuadFacts Q hQ).2.2.1 x (y + y'),
        (Work.HP.MDEstimates.polarQuadFacts Q hQ).2.2.1 x y,
        (Work.HP.MDEstimates.polarQuadFacts Q hQ).2.2.1 x y']
      exact (Work.HP.MDEstimates.polarQuadFacts Q hQ).1 y y' x)
    (fun c x y => by
      rw [(Work.HP.MDEstimates.polarQuadFacts Q hQ).2.2.1 x (c • y),
        (Work.HP.MDEstimates.polarQuadFacts Q hQ).2.2.1 x y]
      exact (Work.HP.MDEstimates.polarQuadFacts Q hQ).2.1 c y x)

lemma polB_apply (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (x y : Fin 5 → ℚ) : polB Q hQ x y = Work.HP.MDEstimates.polQ Q x y := rfl

lemma polB_comm (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (x y : Fin 5 → ℚ) : polB Q hQ x y = polB Q hQ y x :=
  (Work.HP.MDEstimates.polarQuadFacts Q hQ).2.2.1 x y

lemma polB_self (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (x : Fin 5 → ℚ) : polB Q hQ x x = MvPolynomial.eval x Q :=
  (Work.HP.MDEstimates.polarQuadFacts Q hQ).2.2.2.1 x

lemma mem_ker_polB_iff (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (v : Fin 5 → ℚ) : v ∈ LinearMap.ker (polB Q hQ) ↔ v ∈ Work.HP.MDEstimates.radQ Q := by
  constructor
  · intro h w
    have hh := LinearMap.ext_iff.mp (LinearMap.mem_ker.mp h) w
    rw [polB_apply] at hh
    simpa using hh
  · intro h
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro w
    simpa [polB_apply] using h w

/-- `Q` vanishes on a submodule `P` iff `P` is totally isotropic for the polar form. -/
lemma vanish_iff_orth {Q : MvPolynomial (Fin 5) ℚ} (hQ : Q.IsHomogeneous 2)
    (P : Submodule ℚ (Fin 5 → ℚ)) :
    (∀ v ∈ P, MvPolynomial.eval v Q = 0) ↔
      (∀ u ∈ P, ∀ v ∈ P, polB Q hQ u v = 0) := by
  constructor
  · intro h u hu v hv
    have huv : u + v ∈ P := P.add_mem hu hv
    have h1 : MvPolynomial.eval (u + v) Q = 0 := h (u + v) huv
    have h2 : MvPolynomial.eval u Q = 0 := h u hu
    have h3 : MvPolynomial.eval v Q = 0 := h v hv
    have key : polB Q hQ (u + v) (u + v)
        = polB Q hQ u u + polB Q hQ u v + polB Q hQ v u + polB Q hQ v v := by
      simp only [map_add, LinearMap.add_apply]
      ring
    have hpol : MvPolynomial.eval (u + v) Q
        = MvPolynomial.eval u Q + MvPolynomial.eval v Q + 2 * polB Q hQ u v := by
      rw [← polB_self Q hQ (u + v), key, polB_self Q hQ u, polB_self Q hQ v,
        polB_comm Q hQ v u]
      ring
    rw [h1, h2, h3] at hpol
    linarith
  · intro h v hv
    rw [← polB_self Q hQ v]
    exact h v hv v hv

/-! ## A nonzero symmetric bilinear form on a `3`-dimensional space has ≤ `2` isotropic
`2`-planes (delegated). -/

-- In a vector space of dimension `3` over a field `K` with `2 ≠ 0`, a symmetric bilinear
-- form that is not identically zero on the diagonal has at most two totally isotropic
-- `2`-planes.  (A local proof, independent of the delegated module of the same name.)
private theorem twoIsotropicPlanes_le_aux {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (b : V →ₗ[K] V →ₗ[K] K) (hsymm : ∀ x y, b x y = b y x)
    (hfin : Module.finrank K V = 3) (hne : ∃ u, b u u ≠ 0) :
    ∃ S : Finset (Submodule K V), S.card ≤ 2 ∧
      ∀ L : Submodule K V, Module.finrank K L = 2 → (∀ x ∈ L, b x x = 0) → L ∈ S := by
  classical
  -- Polarisation: diagonal vanishing on a submodule gives full isotropy.
  have iso_full : ∀ L : Submodule K V, (∀ x ∈ L, b x x = 0) → ∀ x ∈ L, ∀ y ∈ L, b x y = 0 := by
    intro L hL x hx y hy
    have h2' : (2 : K) * b x y = 0 := by
      have key : b (x + y) (x + y) = b x x + 2 * b x y + b y y := by
        simp only [map_add, LinearMap.add_apply]
        rw [hsymm y x]
        ring
      rw [hL (x + y) (L.add_mem hx hy), hL x hx, hL y hy] at key
      simpa using key.symm
    exact (mul_eq_zero.mp h2').resolve_left h2
  by_cases hT : ∃ L₁ L₂ : Submodule K V, Module.finrank K L₁ = 2 ∧
      Module.finrank K L₂ = 2 ∧ (∀ x ∈ L₁, b x x = 0) ∧ (∀ x ∈ L₂, b x x = 0) ∧ L₁ ≠ L₂
  · obtain ⟨L₁, L₂, hd1, hd2, hi1, hi2, h12⟩ := hT
    have hi1' := iso_full L₁ hi1
    have hi2' := iso_full L₂ hi2
    set m := L₁ ⊓ L₂ with hm
    have hmle1 : m ≤ L₁ := inf_le_left
    have hmle2 : m ≤ L₂ := inf_le_right
    have hmne1 : m ≠ L₁ := by
      intro heq
      have hle : L₁ ≤ L₂ := heq ▸ hmle2
      exact h12 (Submodule.eq_of_le_of_finrank_le hle (by rw [hd2, hd1]))
    have hm1 : Module.finrank K ↥m = 1 := by
      have hfs := Submodule.finrank_sup_add_finrank_inf_eq L₁ L₂
      rw [← hm] at hfs
      have hle3 : Module.finrank K ↥(L₁ ⊔ L₂) ≤ 3 := by
        have h := Submodule.finrank_mono (le_top : L₁ ⊔ L₂ ≤ (⊤ : Submodule K V))
        rwa [finrank_top, hfin] at h
      have hmle2' : Module.finrank K ↥m ≤ 2 := by
        have h := Submodule.finrank_mono hmle1
        rwa [hd1] at h
      have hmne2 : Module.finrank K ↥m ≠ 2 := by
        intro hh
        exact hmne1 (Submodule.eq_of_le_of_finrank_eq hmle1 (by rw [hh, hd1]))
      rw [hd1, hd2] at hfs
      omega
    have hm0 : ∃ m₀ ∈ m, m₀ ≠ 0 := (Submodule.ne_bot_iff m).mp (by
      intro hbot
      rw [hbot, finrank_bot] at hm1
      exact Nat.zero_ne_one hm1)
    obtain ⟨m₀, hm0m, hm0ne⟩ := hm0
    have hlt1 : m < L₁ := lt_of_le_of_ne hmle1 hmne1
    obtain ⟨a, haL1, ham⟩ := SetLike.exists_of_lt hlt1
    have hmne2 : m ≠ L₂ := by
      intro heq
      have hle : L₂ ≤ L₁ := heq ▸ hmle1
      exact h12 (Submodule.eq_of_le_of_finrank_le hle (by rw [hd1, hd2])).symm
    have hlt2 : m < L₂ := lt_of_le_of_ne hmle2 hmne2
    obtain ⟨bp, hbpL2, hbpm⟩ := SetLike.exists_of_lt hlt2
    have hbpL1 : bp ∉ L₁ := fun h => hbpm (Submodule.mem_inf.mpr ⟨h, hbpL2⟩)
    have hane : a ≠ 0 := fun h0 => ham (h0 ▸ Submodule.zero_mem m)
    have hbpne : bp ≠ 0 := fun h0 => hbpm (h0 ▸ Submodule.zero_mem m)
    have hmeq : m = K ∙ m₀ := by
      refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
      · exact (Submodule.span_singleton_le_iff_mem m₀ m).mpr hm0m
      · rw [hm1, finrank_span_singleton hm0ne]
    have hL1a : L₁ = K ∙ m₀ ⊔ K ∙ a := by
      have hle : K ∙ m₀ ⊔ K ∙ a ≤ L₁ := sup_le
        ((Submodule.span_singleton_le_iff_mem m₀ L₁).mpr (hmle1 hm0m))
        ((Submodule.span_singleton_le_iff_mem a L₁).mpr haL1)
      have hfr : Module.finrank K ↥(K ∙ m₀ ⊔ K ∙ a) = 2 := by
        have hfs := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ m₀) (K ∙ a)
        have h1 : Module.finrank K ↥(K ∙ m₀) = 1 := finrank_span_singleton hm0ne
        have h2' : Module.finrank K ↥(K ∙ a) = 1 := finrank_span_singleton hane
        have hdisj : K ∙ m₀ ⊓ K ∙ a = ⊥ := by
          rw [eq_bot_iff]
          intro z hz
          rw [Submodule.mem_bot]
          obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.mp hz
          have hz1m : z ∈ m := hmeq ▸ hz1
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz2
          by_cases hc0 : c = 0
          · rw [hc0, zero_smul] at hc; exact hc.symm
          · exfalso
            have haz : a = c⁻¹ • z := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
            exact ham (haz ▸ m.smul_mem _ hz1m)
        rw [hdisj, finrank_bot, h1, h2'] at hfs
        omega
      exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, hd1])).symm
    have hL2a : L₂ = K ∙ m₀ ⊔ K ∙ bp := by
      have hle : K ∙ m₀ ⊔ K ∙ bp ≤ L₂ := sup_le
        ((Submodule.span_singleton_le_iff_mem m₀ L₂).mpr (hmle2 hm0m))
        ((Submodule.span_singleton_le_iff_mem bp L₂).mpr hbpL2)
      have hfr : Module.finrank K ↥(K ∙ m₀ ⊔ K ∙ bp) = 2 := by
        have hfs := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ m₀) (K ∙ bp)
        have h1 : Module.finrank K ↥(K ∙ m₀) = 1 := finrank_span_singleton hm0ne
        have h2' : Module.finrank K ↥(K ∙ bp) = 1 := finrank_span_singleton hbpne
        have hdisj : K ∙ m₀ ⊓ K ∙ bp = ⊥ := by
          rw [eq_bot_iff]
          intro z hz
          rw [Submodule.mem_bot]
          obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.mp hz
          have hz1m : z ∈ m := hmeq ▸ hz1
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz2
          by_cases hc0 : c = 0
          · rw [hc0, zero_smul] at hc; exact hc.symm
          · exfalso
            have hbz : bp = c⁻¹ • z := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
            exact hbpm (hbz ▸ m.smul_mem _ hz1m)
        rw [hdisj, finrank_bot, h1, h2'] at hfs
        omega
      exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, hd2])).symm
    have hV12 : L₁ ⊔ L₂ = ⊤ := by
      have h3 : Module.finrank K ↥(L₁ ⊔ L₂) = 3 := by
        have hfs := Submodule.finrank_sup_add_finrank_inf_eq L₁ L₂
        rw [← hm, hd1, hd2, hm1] at hfs
        omega
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [h3, hfin]
    have hVtop : (K ∙ m₀ ⊔ K ∙ a) ⊔ K ∙ bp = ⊤ := by
      have h3 : Module.finrank K ↥((K ∙ m₀ ⊔ K ∙ a) ⊔ K ∙ bp) = 3 := by
        have hfs := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ m₀ ⊔ K ∙ a) (K ∙ bp)
        have hfA : Module.finrank K ↥(K ∙ m₀ ⊔ K ∙ a) = 2 := by rw [← hL1a, hd1]
        have hfB : Module.finrank K ↥(K ∙ bp) = 1 := finrank_span_singleton hbpne
        have hdisj : (K ∙ m₀ ⊔ K ∙ a) ⊓ K ∙ bp = ⊥ := by
          rw [eq_bot_iff]
          intro z hz
          rw [Submodule.mem_bot]
          obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.mp hz
          have hz1L1 : z ∈ L₁ := hL1a ▸ hz1
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz2
          by_cases hc0 : c = 0
          · rw [hc0, zero_smul] at hc; exact hc.symm
          · exfalso
            have hbz : bp = c⁻¹ • z := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
            exact hbpL1 (hbz ▸ L₁.smul_mem _ hz1L1)
        rw [hdisj, finrank_bot, hfA, hfB] at hfs
        omega
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [h3, hfin]
    have haa : b a a = 0 := hi1' a haL1 a haL1
    have hbb : b bp bp = 0 := hi2' bp hbpL2 bp hbpL2
    -- The key identity
    have hident : ∀ x : V, b a bp * b x x = 2 * (b a x) * (b bp x) := by
      intro x
      have hx : x ∈ (K ∙ m₀ ⊔ K ∙ a) ⊔ K ∙ bp := by rw [hVtop]; trivial
      obtain ⟨y, hy, r, hr, hyr⟩ := Submodule.mem_sup.mp hx
      obtain ⟨t, ht, s, hs, hts⟩ := Submodule.mem_sup.mp hy
      obtain ⟨t0, ht0⟩ := Submodule.mem_span_singleton.mp ht
      obtain ⟨s0, hs0⟩ := Submodule.mem_span_singleton.mp hs
      obtain ⟨r0, hr0⟩ := Submodule.mem_span_singleton.mp hr
      have hx' : x = (t0 • m₀ + s0 • a) + r0 • bp := by
        rw [← hyr, ← hts, ← ht0, ← hs0, ← hr0]
      have hbrad : ∀ z, b m₀ z = 0 := by
        intro z
        have hz : z ∈ L₁ ⊔ L₂ := by rw [hV12]; trivial
        obtain ⟨l₁, hl₁, l₂, hl₂, hlz⟩ := Submodule.mem_sup.mp hz
        rw [← hlz, map_add,
          hi1' m₀ (hmle1 hm0m) l₁ hl₁, hi2' m₀ (hmle2 hm0m) l₂ hl₂, add_zero]
      have hbrad' : ∀ z, b z m₀ = 0 := fun z => by rw [hsymm]; exact hbrad z
      have hphi : b a x = r0 * b a bp := by
        rw [hx']
        simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
          hbrad, hbrad', haa, hsymm a m₀]
        ring
      have hpsi : b bp x = s0 * b a bp := by
        rw [hx']
        simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
          hbrad, hbrad', hbb, hsymm bp a]
        ring
      have hxx : b x x = 2 * s0 * r0 * b a bp := by
        rw [hx']
        simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
          hbrad, hbrad', haa, hbb, hsymm bp a]
        ring
      rw [hxx, hphi, hpsi]
      ring
    -- λ ≠ 0
    have hlamne : b a bp ≠ 0 := by
      intro hlam0
      have hspanS : Submodule.span K ({m₀, a, bp} : Set V) = ⊤ := by
        refine le_antisymm le_top ?_
        rw [← hVtop]
        refine sup_le (sup_le ?_ ?_) ?_
        · rw [Submodule.span_singleton_le_iff_mem]; exact Submodule.subset_span (by simp)
        · rw [Submodule.span_singleton_le_iff_mem]; exact Submodule.subset_span (by simp)
        · rw [Submodule.span_singleton_le_iff_mem]; exact Submodule.subset_span (by simp)
      have hpair : ∀ x ∈ ({m₀, a, bp} : Set V), ∀ y ∈ ({m₀, a, bp} : Set V), b x y = 0 := by
        intro x hx y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        rcases hx with hx1 | hx1 | hx1 <;> rcases hy with hy1 | hy1 | hy1 <;> rw [hx1, hy1]
        · exact hi1' m₀ (hmle1 hm0m) m₀ (hmle1 hm0m)
        · exact hi1' m₀ (hmle1 hm0m) a haL1
        · exact hi2' m₀ (hmle2 hm0m) bp hbpL2
        · exact hi1' a haL1 m₀ (hmle1 hm0m)
        · exact hi1' a haL1 a haL1
        · exact hlam0
        · exact hi2' bp hbpL2 m₀ (hmle2 hm0m)
        · rw [hsymm]; exact hlam0
        · exact hi2' bp hbpL2 bp hbpL2
      have hb_eq : b = 0 := by
        refine LinearMap.ext_on hspanS (fun x hx => ?_)
        refine LinearMap.ext_on hspanS (fun y hy => ?_)
        exact hpair x hx y hy
      obtain ⟨u, hu⟩ := hne
      exact hu (by rw [hb_eq]; rfl)
    have hbpa : b bp a = b a bp := hsymm bp a
    have hker_phi : LinearMap.ker (b a) = L₁ := by
      have hle : L₁ ≤ LinearMap.ker (b a) := fun z hz => LinearMap.mem_ker.mpr (hi1' a haL1 z hz)
      have hfr : Module.finrank K ↥(LinearMap.ker (b a)) = 2 := by
        have h := LinearMap.finrank_range_add_finrank_ker (b a)
        have hsurj : Function.Surjective (b a) := fun c =>
          ⟨(c / (b a bp)) • bp, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hlamne]⟩
        have hran : (b a).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
        have h1 : Module.finrank K ↥(b a).range = 1 := by
          rw [hran, finrank_top, Module.finrank_self]
        rw [h1, hfin] at h
        omega
      exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, hd1])).symm
    have hker_psi : LinearMap.ker (b bp) = L₂ := by
      have hle : L₂ ≤ LinearMap.ker (b bp) := fun z hz => LinearMap.mem_ker.mpr (hi2' bp hbpL2 z hz)
      have hfr : Module.finrank K ↥(LinearMap.ker (b bp)) = 2 := by
        have h := LinearMap.finrank_range_add_finrank_ker (b bp)
        have hne' : b bp a ≠ 0 := by rw [hbpa]; exact hlamne
        have hsurj : Function.Surjective (b bp) := fun c =>
          ⟨(c / (b bp a)) • a, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hne']⟩
        have hran : (b bp).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
        have h1 : Module.finrank K ↥(b bp).range = 1 := by
          rw [hran, finrank_top, Module.finrank_self]
        rw [h1, hfin] at h
        omega
      exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, hd2])).symm
    have hcover : ∀ L : Submodule K V, Module.finrank K L = 2 → (∀ x ∈ L, b x x = 0) →
        L = L₁ ∨ L = L₂ := by
      intro L hdL hiL
      have hsub : ∀ x ∈ L, x ∈ L₁ ∨ x ∈ L₂ := by
        intro x hxL
        have hbxx : b x x = 0 := hiL x hxL
        have hprod : (b a x) * (b bp x) = 0 := by
          have h := hident x
          rw [hbxx, mul_zero] at h
          have h2' : (2 : K) * ((b a x) * (b bp x)) = 0 := by rw [← mul_assoc, h.symm]
          exact (mul_eq_zero.mp h2').resolve_left h2
        rcases mul_eq_zero.mp hprod with hz | hz
        · left; rw [← hker_phi]; exact LinearMap.mem_ker.mpr hz
        · right; rw [← hker_psi]; exact LinearMap.mem_ker.mpr hz
      by_contra h
      rw [not_or] at h
      obtain ⟨hne1, hne2⟩ := h
      have hnl1 : ¬ L ≤ L₁ := fun hle => hne1 (Submodule.eq_of_le_of_finrank_le hle (by rw [hd1, hdL]))
      have hnl2 : ¬ L ≤ L₂ := fun hle => hne2 (Submodule.eq_of_le_of_finrank_le hle (by rw [hd2, hdL]))
      obtain ⟨u, huL, huL1⟩ := SetLike.not_le_iff_exists.mp hnl1
      obtain ⟨w, hwL, hwL2⟩ := SetLike.not_le_iff_exists.mp hnl2
      have huL2 : u ∈ L₂ := (hsub u huL).resolve_left huL1
      have hwL1 : w ∈ L₁ := (hsub w hwL).resolve_right hwL2
      have hzL : u + w ∈ L := L.add_mem huL hwL
      rcases hsub (u + w) hzL with hz | hz
      · refine huL1 ?_
        have : u = (u + w) - w := by abel
        rw [this]; exact L₁.sub_mem hz hwL1
      · refine hwL2 ?_
        have : w = (u + w) - u := by abel
        rw [this]; exact L₂.sub_mem hz huL2
    refine ⟨{L₁, L₂}, Finset.card_le_two, ?_⟩
    intro L hdL hiL
    rcases hcover L hdL hiL with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · by_cases hE : ∃ L : Submodule K V, Module.finrank K L = 2 ∧ (∀ x ∈ L, b x x = 0)
    · obtain ⟨L₀, hd0, hi0⟩ := hE
      refine ⟨{L₀}, by simp, ?_⟩
      intro L hdL hiL
      rw [Finset.mem_singleton]
      by_contra hne
      exact hT ⟨L, L₀, hdL, hd0, hiL, hi0, hne⟩
    · refine ⟨∅, by simp, ?_⟩
      intro L hdL hiL
      exact absurd ⟨L, hdL, hiL⟩ hE

/-! ## The main statement -/

theorem planesNotRadFinset (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0)
    (hnolf : ∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ Q → False)
    {x : Fin 5 → ℚ} (hx : MvPolynomial.eval x Q = 0) (hxR : x ∉ Work.HP.MDEstimates.radQ Q) :
    ∃ S : Finset (Submodule ℚ (Fin 5 → ℚ)), S.card ≤ 2 ∧
      ∀ P : Submodule ℚ (Fin 5 → ℚ), Module.finrank ℚ P = 3 → x ∈ P →
        (∀ v ∈ P, MvPolynomial.eval v Q = 0) → P ∈ S := by
  classical
  set B := polB Q hQ with hB
  -- `B x` is a nonzero linear functional, because `x ∉ radQ Q`.
  have hφne : B x ≠ 0 := by
    intro h0
    refine hxR ((mem_ker_polB_iff Q hQ x).mp ?_)
    rw [LinearMap.mem_ker]
    exact h0
  obtain ⟨z, hz⟩ : ∃ z, B x z ≠ 0 := by
    by_contra h
    rw [not_exists] at h
    exact hφne (LinearMap.ext (fun w => by simpa using h w))
  have hsurj : Function.Surjective (B x) := fun c =>
    ⟨(c / (B x z)) • z, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hz]⟩
  have hran : (B x).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  -- `W = x^⊥`, a hyperplane.
  set W : Submodule ℚ (Fin 5 → ℚ) := LinearMap.ker (B x) with hW
  have hxW : x ∈ W := by rw [hW, LinearMap.mem_ker, polB_self, hx]
  have hxne : x ≠ 0 := by
    rintro rfl
    exact hxR ((mem_ker_polB_iff Q hQ 0).mp (Submodule.zero_mem (LinearMap.ker (polB Q hQ))))
  have hfinW : Module.finrank ℚ W = 4 := by
    rw [hW]
    have h := LinearMap.finrank_range_add_finrank_ker (B x)
    have h1 : Module.finrank ℚ ↥(B x).range = 1 := by
      rw [hran, finrank_top, Module.finrank_self]
    rw [h1, Module.finrank_fin_fun] at h
    omega
  -- `H` is a complement of `ℚ x` inside `W`, hence `3`-dimensional.
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Submodule.span ℚ ({x} : Set (Fin 5 → ℚ)))
  set H : Submodule ℚ (Fin 5 → ℚ) := C ⊓ W with hH
  have hspanxW : Submodule.span ℚ ({x} : Set (Fin 5 → ℚ)) ≤ W := by
    rw [Submodule.span_le]; simp [hxW]
  have hinf : Submodule.span ℚ ({x} : Set (Fin 5 → ℚ)) ⊓ H = ⊥ := by
    rw [hH]
    refine le_bot_iff.mp ?_
    calc Submodule.span ℚ ({x} : Set (Fin 5 → ℚ)) ⊓ (C ⊓ W)
        ≤ Submodule.span ℚ ({x} : Set (Fin 5 → ℚ)) ⊓ C := inf_le_inf_left _ inf_le_left
      _ = ⊥ := hC.inf_eq_bot
  have hsup : Submodule.span ℚ ({x} : Set (Fin 5 → ℚ)) ⊔ H = W := by
    refine le_antisymm (sup_le hspanxW (by rw [hH]; exact inf_le_right)) ?_
    intro w hw
    have hwtop : w ∈ (⊤ : Submodule ℚ (Fin 5 → ℚ)) := Submodule.mem_top
    rw [← hC.sup_eq_top] at hwtop
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hwtop
    rw [Submodule.mem_sup]
    refine ⟨a, ha, c, ?_, hac⟩
    rw [hH]
    refine ⟨hc, ?_⟩
    have hcW : c ∈ W := by
      have : c = w - a := by rw [← hac]; abel
      rw [this]; exact W.sub_mem hw (hspanxW ha)
    exact hcW
  have hfinx : Module.finrank ℚ (Submodule.span ℚ ({x} : Set (Fin 5 → ℚ))) = 1 :=
    finrank_span_singleton hxne
  have hfinH : Module.finrank ℚ H = 3 := by
    have hfs := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span ℚ ({x} : Set (Fin 5 → ℚ))) H
    rw [hsup, hinf, hfinW, hfinx, finrank_bot] at hfs
    omega
  -- The restricted bilinear form `b` on `H`.
  let b : ↥H →ₗ[ℚ] ↥H →ₗ[ℚ] ℚ :=
    LinearMap.mk₂ ℚ (fun u v => B (u : Fin 5 → ℚ) v)
      (fun u u' v => by
        show B ((u : Fin 5 → ℚ) + u') v = B u v + B u' v
        rw [map_add, LinearMap.add_apply])
      (fun c u v => by
        show B (c • (u : Fin 5 → ℚ)) v = c * B u v
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul])
      (fun u v v' => by
        show B (u : Fin 5 → ℚ) ((v : Fin 5 → ℚ) + v') = B u v + B u v'
        rw [map_add])
      (fun c u v => by
        show B (u : Fin 5 → ℚ) (c • (v : Fin 5 → ℚ)) = c * B u v
        rw [map_smul, smul_eq_mul])
  have hbapply : ∀ u v : ↥H, b u v = B (u : Fin 5 → ℚ) v := fun _ _ => rfl
  have hgsym : ∀ u v : ↥H, b u v = b v u := fun u v => polB_comm Q hQ u v
  have hHW : H ≤ W := by rw [hH]; exact inf_le_right
  -- `b ≠ 0`: otherwise `Q` vanishes on the hyperplane `W`, forcing a linear factor of `Q`.
  have hg0 : b ≠ 0 := by
    intro hb0
    have hQW : ∀ v ∈ W, MvPolynomial.eval v Q = 0 := by
      intro v hv
      rw [← polB_self Q hQ v]
      have hv' : v ∈ Submodule.span ℚ ({x} : Set (Fin 5 → ℚ)) ⊔ H := by rw [hsup]; exact hv
      obtain ⟨v₁, hv₁, v₂, hv₂, hveq⟩ := Submodule.mem_sup.mp hv'
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv₁
      have hxv₂ : B x v₂ = 0 := LinearMap.mem_ker.mp (hW ▸ hHW hv₂)
      have hxx : B x x = 0 := by rw [polB_self, hx]
      have hv₂v₂ : B v₂ v₂ = 0 := by
        have h0 : b ⟨v₂, hv₂⟩ ⟨v₂, hv₂⟩ = 0 := by simp [hb0]
        exact h0
      have hv₂x : B v₂ x = 0 := by rw [polB_comm Q hQ v₂ x]; exact hxv₂
      rw [← hveq]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [hxx, hxv₂, hv₂x, hv₂v₂]
      ring
    obtain ⟨ℓ, hℓ, hdvd⟩ := Work.HP.MDEstimates.hyperplaneFactor Q hQ W hfinW hQW
    exact hnolf ℓ hℓ hdvd
  -- Hence `b` does not vanish identically on the diagonal.
  have hneH : ∃ u : ↥H, b u u ≠ 0 := by
    by_contra h
    apply hg0
    refine LinearMap.ext (fun u => LinearMap.ext (fun v => ?_))
    have hu : b u u = 0 := by by_contra hc; exact h ⟨u, hc⟩
    have hv : b v v = 0 := by by_contra hc; exact h ⟨v, hc⟩
    have huv : b (u + v) (u + v) = 0 := by by_contra hc; exact h ⟨u + v, hc⟩
    have key : b (u + v) (u + v) = b u u + b u v + b v u + b v v := by
      simp only [map_add, LinearMap.add_apply]
      ring
    rw [huv, hu, hv, hgsym v u] at key
    have h2 : (2 : ℚ) * b u v = 0 := by linarith
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  -- The abstract count of isotropic `2`-planes of `H`.
  obtain ⟨S_H, hcardH, hcoverH⟩ :=
    twoIsotropicPlanes_le_aux (V := ↥H) (by norm_num) b hgsym hfinH hneH
  -- Valid planes `P` land in `S_H` via `P ↦ H ⊓ P`, and are recovered as `ℚx ⊔ (H ⊓ P)`.
  refine ⟨S_H.image (fun L => Submodule.span ℚ ({x} : Set (Fin 5 → ℚ)) ⊔ L.map H.subtype),
    ?_, ?_⟩
  · calc (S_H.image (fun L => Submodule.span ℚ ({x} : Set (Fin 5 → ℚ)) ⊔ L.map H.subtype)).card
        ≤ S_H.card := Finset.card_image_le
      _ ≤ 2 := hcardH
  · intro P hfP hxP hvP
    have hPleW : P ≤ W := by
      intro p hp
      rw [hW]
      refine LinearMap.mem_ker.mpr ?_
      rw [polB_comm Q hQ x p]
      exact (vanish_iff_orth hQ P).mp hvP p hp x hxP
    have hspanP : Submodule.span ℚ ({x} : Set (Fin 5 → ℚ)) ≤ P := by
      rw [Submodule.span_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      exact hy ▸ hxP
    have hsplitP : P = Submodule.span ℚ ({x} : Set (Fin 5 → ℚ)) ⊔ (H ⊓ P) := by
      refine le_antisymm ?_ ?_
      · intro p hp
        have hpW : p ∈ W := hPleW hp
        rw [← hsup] at hpW
        obtain ⟨a, ha, h, hh, hah⟩ := Submodule.mem_sup.mp hpW
        rw [Submodule.mem_sup]
        refine ⟨a, ha, h, ⟨hh, ?_⟩, hah⟩
        have : h = p - a := by rw [← hah]; abel
        rw [this]
        exact P.sub_mem hp (hspanP ha)
      · exact sup_le hspanP inf_le_right
    have hfinHP : Module.finrank ℚ ↥(H ⊓ P) = 2 := by
      have hinf' : Submodule.span ℚ ({x} : Set (Fin 5 → ℚ)) ⊓ (H ⊓ P) = ⊥ := by
        rw [← inf_assoc, hinf, bot_inf_eq]
      have hfs := Submodule.finrank_sup_add_finrank_inf_eq
        (Submodule.span ℚ ({x} : Set (Fin 5 → ℚ))) (H ⊓ P)
      rw [← hsplitP, hinf', hfinx, hfP, finrank_bot] at hfs
      omega
    have hfinComap : Module.finrank ℚ ↥(Submodule.comap H.subtype P) = 2 := by
      have he := LinearEquiv.finrank_eq
        (Submodule.equivMapOfInjective H.subtype H.subtype_injective
          (Submodule.comap H.subtype P))
      rw [he, Submodule.map_comap_eq, Submodule.range_subtype]
      exact hfinHP
    have hmemH : Submodule.comap H.subtype P ∈ S_H := by
      apply hcoverH
      · exact hfinComap
      · intro u hu
        exact (vanish_iff_orth hQ P).mp hvP u.val (Submodule.mem_comap.mp hu) u.val
          (Submodule.mem_comap.mp hu)
    refine Finset.mem_image.mpr ⟨Submodule.comap H.subtype P, hmemH, ?_⟩
    show Submodule.span ℚ ({x} : Set (Fin 5 → ℚ)) ⊔ (Submodule.comap H.subtype P).map H.subtype = P
    rw [Submodule.map_comap_eq, Submodule.range_subtype]
    exact hsplitP.symm

end Work.HP.Q44Main.QuadCount
