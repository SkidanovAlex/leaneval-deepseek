import Mathlib
import Submission.Work.ThmG.Defs
import Submission.Work.ThmG.sum_deg_sq_excludingKernel
import Submission.Work.ThmG.resFun_indFun_eq_of_vanishes_off_hall
import Submission.Work.ThmG.arith_case
import Submission.Work.ThmG.rankOne_index
import Submission.Work.CharCore.Main
import Submission.Work.Coherence.All
import Submission.Work.Induction.All
import Submission.Work.CohApps.sum_irr_deg_sq_le_ker
import Submission.Work.ThmG.restriction_degree_count
import Submission.Work.ThmG.trivial_on_Q1_of_orthogonal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

noncomputable section

open Classical

namespace Work.ThmG

theorem degree_count_engine {G : Type} [Group G] [Fintype G] {H Q D S Q₁ : Subgroup G}
    [Fintype ↥H] {lam : ↥H → ℂ} {f₁ f₂ : G → ℂ}
    (hQ₁H : Q₁ ≤ H) (hQ₁N : (Q₁.subgroupOf H).Normal)
    (hQn : H ≤ Subgroup.normalizer (Q : Set G))
    (hTI : ∀ x : G, x ∉ H → Q ⊓ Submission.Blueprint.conj x Q = ⊥)
    (hsup : Q ⊔ D = H) (hinf : Q ⊓ D = ⊥)
    (hcop : Nat.Coprime (Nat.card D) (Nat.card Q))
    (hD3 : 3 ≤ Nat.card D)
    (hS2 : 2 ≤ Nat.card S) (hQ₁3 : 3 ≤ Nat.card Q₁)
    (hcardH : Nat.card H = Nat.card Q * Nat.card D)
    (hcardQ : Nat.card Q = Nat.card S * Nat.card Q₁)
    (hindex : (Q₁.subgroupOf H).index = Nat.card S * Nat.card D)
    (hcoh : Work.Coherence.Coherent (Submission.Blueprint.excludingKernel H Q₁)
      (Submission.Blueprint.indLinear H))
    (hcard2 : 2 ≤ (Submission.Blueprint.excludingKernel H Q₁).card)
    (hvan : ∀ χ ∈ Submission.Blueprint.excludingKernel H Q₁, ∀ h : ↥H, (h : G) ∉ Q → χ h = 0)
    (hdeg : ∃ χ₀ ∈ Submission.Blueprint.excludingKernel H Q₁, χ₀ 1 = (Nat.card D : ℂ) ∧
        ∀ ψ ∈ Submission.Blueprint.excludingKernel H Q₁, ∃ a : ℕ, ψ 1 = (a : ℂ) * χ₀ 1)
    (hlam : lam ∈ Work.CharCore.Irr ↥H) (hlam1 : lam 1 = 1)
    (hlamQ : ∀ x : ↥H, (x : G) ∈ Q → lam x = 1)
    (hlamne : lam ≠ (fun _ : ↥H => (1 : ℂ)))
    (hf1 : f₁ ∈ Work.CharCore.Irr G) (hf2 : f₂ ∈ Work.CharCore.Irr G) (hfne : f₁ ≠ f₂)
    (hind : Work.Induction.indFun H lam = f₁ + f₂)
    (hindexQ : H.index = Nat.card Q + 1) (hHindexOdd : Odd H.index) :
    ∃ f ∈ Work.CharCore.Irr G, f ≠ (fun _ : G => (1 : ℂ)) ∧
      ∀ x : ↥H, (x : G) ∈ Q₁ → f x = f 1 := by
  classical
  -- `Irr` does not depend on the choice of `Fintype` instance on the group
  have hIrr_conv : ∀ {T : Type} [Group T] {i j : Fintype T} (χ : T → ℂ),
      χ ∈ @Work.CharCore.Irr T _ i ↔ χ ∈ @Work.CharCore.Irr T _ j := by
    intro T _ i j χ
    have hmod : @Work.CharCore.irrSubmodules T _ i = @Work.CharCore.irrSubmodules T _ j := by
      unfold Work.CharCore.irrSubmodules
      exact congrArg Classical.choose (Subsingleton.elim _ _)
    have h1 : χ ∈ @Work.CharCore.Irr T _ i ↔
        ∃ N ∈ @Work.CharCore.irrSubmodules T _ i, (Work.CharCore.submoduleRep N).character = χ :=
      @Work.CharCore.mem_Irr_iff_exists T _ i χ
    have h2 : χ ∈ @Work.CharCore.Irr T _ j ↔
        ∃ N ∈ @Work.CharCore.irrSubmodules T _ j, (Work.CharCore.submoduleRep N).character = χ :=
      @Work.CharCore.mem_Irr_iff_exists T _ j χ
    rw [h1, h2]
    exact ⟨fun ⟨N, hN, hχ⟩ => ⟨N, by rw [← hmod]; exact hN, hχ⟩,
           fun ⟨N, hN, hχ⟩ => ⟨N, by rw [hmod]; exact hN, hχ⟩⟩
  let Fs : Finset (↥H → ℂ) := Submission.Blueprint.excludingKernel H Q₁
  have hFmem : ∀ χ : ↥H → ℂ, χ ∈ Fs ↔
      χ ∈ Work.CharCore.Irr ↥H ∧ ∃ x : ↥H, (x : G) ∈ Q₁ ∧ χ x ≠ χ 1 := by
    intro χ
    have h2 : χ ∈ Fs ↔ χ ∈ (Work.CharCore.Irr ↥H).filter
        (fun χ => ∃ x : ↥H, (x : G) ∈ Q₁ ∧ χ x ≠ χ 1) := by
      dsimp only [Fs, Submission.Blueprint.excludingKernel]
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨(hIrr_conv χ).mp h.1, h.2⟩,
             fun h => ⟨(hIrr_conv χ).mpr h.1, h.2⟩⟩
    rw [h2]
    exact Finset.mem_filter
  have hFirr : ∀ χ ∈ Fs, χ ∈ Work.CharCore.Irr ↥H := fun χ hχ => ((hFmem χ).mp hχ).1
  have horth : Work.Coherence.Orthonormal Fs :=
    Work.Coherence.irr_orthonormal_finset
      (fun χ hχ => (Work.CharCore.mem_Irr_iff_coherence).mp (hFirr χ hχ))
  -- integral scaling of the inner product, in both relevant types
  have hzsr : ∀ {T : Type} [Group T] [Fintype T] (n : ℤ) (f g : T → ℂ),
      Work.CharCore.cfInner f (n • g) = (n : ℂ) * Work.CharCore.cfInner f g := by
    intro T _ _ n f g
    rw [← Int.cast_smul_eq_zsmul ℂ n g, Work.CharCore.cfInner_smul_right, map_intCast]
  -- the value of `cfInner` does not depend on the choice of `Fintype` instance
  have hinst_eq : ∀ {T : Type} [Group T] {i j : Fintype T} (f g : T → ℂ),
      @Work.CharCore.cfInner T i f g = @Work.CharCore.cfInner T j f g := by
    intro T _ i j f g
    have huniv : @Finset.univ T i = @Finset.univ T j := by ext x; simp
    simp only [Work.CharCore.cfInner, Fintype.card_eq_nat_card, huniv]
  -- coherence package
  obtain ⟨τ', hagree, hiso, hvchar⟩ := hcoh
  have hiso' : ∀ {α β : ↥H → ℂ}, α ∈ Work.Coherence.ZSpan Fs → β ∈ Work.Coherence.ZSpan Fs →
      Work.CharCore.cfInner (τ' α) (τ' β) = Work.CharCore.cfInner α β := by
    intro α β hα hβ
    rw [← Work.CharCore.cfInner_coherence, ← Work.CharCore.cfInner_coherence]
    exact hiso.inner_eq α hα β hβ
  -- the degree-`|D|` character
  obtain ⟨χ₀, hχ₀F, hχ₀deg, hχ₀div⟩ := hdeg
  have hχ₀irr : χ₀ ∈ Work.CharCore.Irr ↥H := hFirr χ₀ hχ₀F
  have hDne : Nat.card D ≠ 0 := by have := hD3; omega
  have hχ₀1ne : χ₀ 1 ≠ 0 := by rw [hχ₀deg]; exact_mod_cast hDne
  -- the degree ratios `A`
  let A : (↥H → ℂ) → ℕ := fun χ => if h : χ ∈ Fs then Classical.choose (hχ₀div χ h) else 0
  have hA : ∀ χ ∈ Fs, χ 1 = (A χ : ℂ) * χ₀ 1 := by
    intro χ hχ
    have hAeq : A χ = Classical.choose (hχ₀div χ hχ) := by
      dsimp only [A]; rw [dif_pos hχ]
    rw [hAeq]
    exact Classical.choose_spec (hχ₀div χ hχ)
  have hA1 : ∀ χ ∈ Fs, 1 ≤ A χ := by
    intro χ hχ
    have h := hA χ hχ
    have hχ1 : χ 1 ≠ 0 := by
      have h2 := Work.CharCore.irrDeg_ne_zero (hFirr χ hχ)
      rwa [← Work.CharCore.irrDeg_spec (hFirr χ hχ)] at h2
    by_contra hcon
    have hzero : A χ = 0 := by omega
    rw [hzero, Nat.cast_zero, zero_mul] at h
    exact hχ1 h
  have hAχ₀ : A χ₀ = 1 := by
    have h := hA χ₀ hχ₀F
    have h2 : ((A χ₀ : ℂ)) = 1 := by
      have h3 : (A χ₀ : ℂ) * χ₀ 1 = 1 * χ₀ 1 := by rw [one_mul]; exact h.symm
      exact mul_right_cancel₀ hχ₀1ne h3
    exact_mod_cast h2
  -- the degree-zero element `χ - A χ · χ₀` lies in `ℤ[S]⁰`
  have hmem0 : ∀ χ ∈ Fs, χ - (A χ : ℤ) • χ₀ ∈ Work.Coherence.ZSpan0 Fs := by
    intro χ hχ
    rw [Work.Coherence.mem_zSpan0]
    refine ⟨?_, ?_⟩
    · exact AddSubgroup.sub_mem _ (Work.Coherence.self_mem_zSpan hχ)
        (AddSubgroup.zsmul_mem _ (Work.Coherence.self_mem_zSpan hχ₀F) (A χ))
    · have h1 : (A χ : ℤ) • χ₀ = (A χ : ℂ) • χ₀ :=
        (Int.cast_smul_eq_zsmul ℂ (A χ) χ₀).symm
      rw [h1]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hA χ hχ]
      ring
  have hτeq : ∀ χ ∈ Fs, Work.Induction.indFun H (χ - (A χ : ℤ) • χ₀)
      = τ' χ - (A χ : ℤ) • τ' χ₀ := by
    intro χ hχ
    have h := hagree _ (hmem0 χ hχ)
    rw [map_sub, map_zsmul] at h
    exact h.symm
  have hτdeg : ∀ χ ∈ Fs, τ' χ 1 = (A χ : ℂ) * τ' χ₀ 1 := by
    intro χ hχ
    have h := congrFun (hτeq χ hχ) 1
    rw [Work.Induction.indFun_apply_one H (χ - (A χ : ℤ) • χ₀)] at h
    have hμ1 : (χ - (A χ : ℤ) • χ₀) 1 = 0 := (Work.Coherence.mem_zSpan0.mp (hmem0 χ hχ)).2
    rw [hμ1, mul_zero, Pi.sub_apply, Pi.smul_apply] at h
    rw [← Int.cast_smul_eq_zsmul ℂ (A χ) (τ' χ₀ 1), smul_eq_mul] at h
    rw [eq_comm, sub_eq_zero] at h
    exact h
  -- `lam` is orthogonal to every member of `S`
  have hlam_ne : ∀ χ ∈ Fs, lam ≠ χ := by
    intro χ hχ hEq
    have hχ1 : χ 1 = (A χ : ℂ) * χ₀ 1 := hA χ hχ
    have hval : ((A χ * Nat.card D : ℕ) : ℂ) = 1 := by
      rw [Nat.cast_mul, ← hχ₀deg, ← hχ1, ← hEq]
      exact hlam1
    have hnat : A χ * Nat.card D = 1 := by exact_mod_cast hval
    have h3 : 3 ≤ A χ * Nat.card D := by
      calc (3:ℕ) = 1 * 3 := by norm_num
        _ ≤ A χ * Nat.card D := Nat.mul_le_mul (hA1 χ hχ) hD3
    omega
  have horth_lam : ∀ χ ∈ Fs, Work.CharCore.cfInner lam χ = 0 := by
    intro χ hχ
    rw [Work.CharCore.irr_orthonormal lam χ hlam (hFirr χ hχ)]
    rw [if_neg (hlam_ne χ hχ)]
  -- `χ - A χ · χ₀` is a class function of degree zero vanishing off `Q`
  have hμclass : ∀ χ ∈ Fs, Work.CharCore.IsClassFun (χ - (A χ : ℤ) • χ₀) := by
    intro χ hχ
    refine Work.CharCore.IsClassFun.sub ?_ ?_
    · exact Work.CharCore.isClassFun_of_mem_Irr (hFirr χ hχ)
    · have h1 : (A χ : ℤ) • χ₀ = (A χ : ℂ) • χ₀ :=
        (Int.cast_smul_eq_zsmul ℂ (A χ) χ₀).symm
      rw [h1]
      exact Work.CharCore.IsClassFun.smul _ (Work.CharCore.isClassFun_of_mem_Irr hχ₀irr)
  have hμvan : ∀ χ ∈ Fs, ∀ h : ↥H, (h : G) ∉ Q → (χ - (A χ : ℤ) • χ₀) h = 0 := by
    intro χ hχ h hh
    have h1 : (A χ : ℤ) • χ₀ = (A χ : ℂ) • χ₀ :=
      (Int.cast_smul_eq_zsmul ℂ (A χ) χ₀).symm
    rw [h1]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hvan χ hχ h hh, hvan χ₀ hχ₀F h hh, mul_zero, sub_zero]
  -- the key orthogonality `⟨Ind λ, Ind(χ - A χ χ₀)⟩ = 0`
  have hmain : ∀ χ ∈ Fs,
      Work.CharCore.cfInner (Work.Induction.indFun H lam) (τ' χ - (A χ : ℤ) • τ' χ₀) = 0 := by
    intro χ hχ
    have hrec : Work.CharCore.cfInner (Work.Induction.indFun H lam)
          (Work.Induction.indFun H (χ - (A χ : ℤ) • χ₀))
        = Work.CharCore.cfInner lam
            (Work.Induction.resFun H (Work.Induction.indFun H (χ - (A χ : ℤ) • χ₀))) :=
      (Work.Induction.frobenius_reciprocity H lam _ (Work.Induction.isClassFun_indFun H _)).trans
        (hinst_eq lam _)
    have hres : Work.Induction.resFun H (Work.Induction.indFun H (χ - (A χ : ℤ) • χ₀))
        = (χ - (A χ : ℤ) • χ₀) :=
      resFun_indFun_eq_of_vanishes_off_hall hsup hinf hcop hQn hTI _
        (hμclass χ hχ) (Work.Coherence.mem_zSpan0.mp (hmem0 χ hχ)).2 (hμvan χ hχ)
    have hμz : Work.CharCore.cfInner lam (χ - (A χ : ℤ) • χ₀) = 0 := by
      rw [Work.CharCore.cfInner_sub_right, hzsr, horth_lam χ hχ, horth_lam χ₀ hχ₀F]
      ring
    rw [← hτeq χ hχ, hrec, congrArg (fun z => Work.CharCore.cfInner lam z) hres, hμz]
  have hstep1 : ∀ χ ∈ Fs, Work.CharCore.cfInner (Work.Induction.indFun H lam) (τ' χ)
      = (A χ : ℂ) * Work.CharCore.cfInner (Work.Induction.indFun H lam) (τ' χ₀) := by
    intro χ hχ
    have h := hmain χ hχ
    rw [Work.CharCore.cfInner_sub_right, hzsr] at h
    rw [sub_eq_zero] at h
    exact h
  -- a signed irreducible is orthogonal to all other irreducibles
  have htau_ne : ∀ χ ∈ Fs, ∀ g : G → ℂ, g ∈ Work.CharCore.Irr G →
      Work.CharCore.cfInner g (τ' χ) ≠ 0 → (τ' χ = g ∨ τ' χ = -g) := by
    intro χ hχ g hg hne
    obtain ⟨ψ, hψc, hcase⟩ := Work.Coherence.isometry_image_irr horth hiso hχ (hvchar χ hχ)
    have hψ : ψ ∈ Work.CharCore.Irr G := (Work.CharCore.mem_Irr_iff_coherence).mpr hψc
    rcases hcase with hcase | hcase
    · rw [hcase, Work.CharCore.irr_orthonormal g ψ hg hψ] at hne
      by_cases hgψ : g = ψ
      · exact Or.inl (by rw [hcase, hgψ])
      · rw [if_neg hgψ] at hne; exact absurd rfl hne
    · rw [hcase, Work.CharCore.cfInner_neg_right, Work.CharCore.irr_orthonormal g ψ hg hψ] at hne
      by_cases hgψ : g = ψ
      · exact Or.inr (by rw [hcase, hgψ])
      · rw [if_neg hgψ, neg_zero] at hne; exact absurd rfl hne
  have hirr_ne_neg : ∀ g h : G → ℂ, g ∈ Work.CharCore.Irr G → h ∈ Work.CharCore.Irr G →
      g ≠ -h := by
    intro g h hg hh hcon
    have hval : g 1 = - h 1 := by rw [hcon]; simp
    rw [Work.CharCore.irrDeg_spec hg, Work.CharCore.irrDeg_spec hh] at hval
    have hre := congrArg Complex.re hval
    simp only [Complex.natCast_re, Complex.neg_re] at hre
    have hgp : (0:ℝ) < (Work.CharCore.irrDeg g : ℝ) := by
      exact_mod_cast Work.CharCore.irrDeg_pos hg
    have hhp : (0:ℝ) < (Work.CharCore.irrDeg h : ℝ) := by
      exact_mod_cast Work.CharCore.irrDeg_pos hh
    linarith
  have heq_or : ∀ {a b c : G → ℂ}, (c = a ∨ c = -a) → (c = b ∨ c = -b) → (a = b ∨ a = -b) := by
    intro a b c ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (by rw [← ha, hb])
    · exact Or.inr (by rw [← ha, hb])
    · have h : -a = b := by rw [← ha, hb]
      exact Or.inr (by rw [← h, neg_neg])
    · have h : -a = -b := by rw [← ha, hb]
      exact Or.inl (neg_inj.mp h)
  -- the central vanishing: `⟨Ind λ, τ' χ₀⟩ = 0`
  have hs0 : Work.CharCore.cfInner (Work.Induction.indFun H lam) (τ' χ₀) = 0 := by
    by_contra hs
    have hpos : 0 < (Fs.erase χ₀).card := by
      rw [Finset.card_erase_of_mem hχ₀F]; omega
    obtain ⟨χ, hχerase⟩ := Finset.card_pos.mp hpos
    have hχF : χ ∈ Fs := Finset.mem_of_mem_erase hχerase
    have hχne : χ ≠ χ₀ := (Finset.mem_erase.mp hχerase).1
    obtain ⟨ψ₀, hψ₀c, hcase₀⟩ :=
      Work.Coherence.isometry_image_irr horth hiso hχ₀F (hvchar χ₀ hχ₀F)
    have hψ₀ : ψ₀ ∈ Work.CharCore.Irr G := (Work.CharCore.mem_Irr_iff_coherence).mpr hψ₀c
    have hsome : f₁ = ψ₀ ∨ f₂ = ψ₀ := by
      by_contra hcon
      push_neg at hcon
      have z1 : Work.CharCore.cfInner f₁ (τ' χ₀) = 0 := by
        rcases hcase₀ with hc | hc
        · rw [hc, Work.CharCore.irr_orthonormal f₁ ψ₀ hf1 hψ₀, if_neg hcon.1]
        · rw [hc, Work.CharCore.cfInner_neg_right,
              Work.CharCore.irr_orthonormal f₁ ψ₀ hf1 hψ₀, if_neg hcon.1, neg_zero]
      have z2 : Work.CharCore.cfInner f₂ (τ' χ₀) = 0 := by
        rcases hcase₀ with hc | hc
        · rw [hc, Work.CharCore.irr_orthonormal f₂ ψ₀ hf2 hψ₀, if_neg hcon.2]
        · rw [hc, Work.CharCore.cfInner_neg_right,
              Work.CharCore.irr_orthonormal f₂ ψ₀ hf2 hψ₀, if_neg hcon.2, neg_zero]
      apply hs
      rw [hind, Work.CharCore.cfInner_add_left, z1, z2, add_zero]
    have contra : ∀ (g h : G → ℂ), g ∈ Work.CharCore.Irr G → h ∈ Work.CharCore.Irr G → g ≠ h →
        Work.Induction.indFun H lam = g + h → (τ' χ₀ = g ∨ τ' χ₀ = -g) → False := by
      intro g h hg hh hgh hadd hrel
      rcases hrel with hrel | hrel
      · have hs1 : Work.CharCore.cfInner (Work.Induction.indFun H lam) (τ' χ₀) = 1 := by
          rw [hadd, hrel, Work.CharCore.cfInner_add_left, Work.CharCore.cfInner_self_mem_Irr hg,
            Work.CharCore.irr_orthonormal h g hh hg, if_neg (Ne.symm hgh), add_zero]
        have hgτ : Work.CharCore.cfInner g (τ' χ) = 0 := by
          rw [← hrel]
          rw [hiso' (Work.Coherence.self_mem_zSpan hχ₀F) (Work.Coherence.self_mem_zSpan hχF)]
          rw [Work.CharCore.irr_orthonormal χ₀ χ hχ₀irr (hFirr χ hχF), if_neg (Ne.symm hχne)]
        have hhτ : Work.CharCore.cfInner h (τ' χ) = (A χ : ℂ) := by
          have hh2 := hstep1 χ hχF
          rw [hs1, mul_one, hadd, Work.CharCore.cfInner_add_left, hgτ, zero_add] at hh2
          exact hh2
        have hne2 : Work.CharCore.cfInner h (τ' χ) ≠ 0 := by
          rw [hhτ]; exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (hA1 χ hχF))
        rcases htau_ne χ hχF h hh hne2 with hh1 | hh1
        · have h1 : Work.CharCore.cfInner h (τ' χ) = 1 := by
            rw [hh1, Work.CharCore.cfInner_self_mem_Irr hh]
          have hAχ : A χ = 1 := by
            have h2 : ((A χ : ℂ)) = 1 := by rw [← hhτ]; exact h1
            exact_mod_cast h2
          have hdeg : (H.index : ℂ) = 2 * (Work.CharCore.irrDeg g : ℂ) := by
            have h1' := congrFun hadd 1
            rw [Work.Induction.indFun_apply_one H lam, hlam1, mul_one, Pi.add_apply,
              ← hrel, ← hh1] at h1'
            rw [hτdeg χ hχF, hAχ, Nat.cast_one, one_mul] at h1'
            have hτ01 : τ' χ₀ 1 = (Work.CharCore.irrDeg g : ℂ) := by
              rw [hrel]; exact Work.CharCore.irrDeg_spec hg
            rw [hτ01] at h1'
            rw [h1']; ring
          have hnat : H.index = 2 * Work.CharCore.irrDeg g := by exact_mod_cast hdeg
          exact Nat.not_even_iff_odd.mpr hHindexOdd
            ⟨Work.CharCore.irrDeg g, by rw [hnat, two_mul]⟩
        · have h1 : Work.CharCore.cfInner h (τ' χ) = -1 := by
            rw [hh1, Work.CharCore.cfInner_neg_right, Work.CharCore.cfInner_self_mem_Irr hh]
          rw [h1] at hhτ
          have hre := congrArg Complex.re hhτ
          simp only [Complex.natCast_re, Complex.neg_re, Complex.one_re] at hre
          have hAle : (1:ℝ) ≤ (A χ : ℝ) := by exact_mod_cast hA1 χ hχF
          linarith
      · have hs1 : Work.CharCore.cfInner (Work.Induction.indFun H lam) (τ' χ₀) = -1 := by
          rw [hadd, hrel, Work.CharCore.cfInner_add_left, Work.CharCore.cfInner_neg_right,
            Work.CharCore.cfInner_neg_right, Work.CharCore.cfInner_self_mem_Irr hg,
            Work.CharCore.irr_orthonormal h g hh hg, if_neg (Ne.symm hgh)]
          ring
        have hgτ : Work.CharCore.cfInner g (τ' χ) = 0 := by
          have hg' : g = - τ' χ₀ := by rw [hrel]; simp
          rw [hg', Work.CharCore.cfInner_neg_left]
          rw [hiso' (Work.Coherence.self_mem_zSpan hχ₀F) (Work.Coherence.self_mem_zSpan hχF)]
          rw [Work.CharCore.irr_orthonormal χ₀ χ hχ₀irr (hFirr χ hχF), if_neg (Ne.symm hχne)]
          ring
        have hhτ : Work.CharCore.cfInner h (τ' χ) = - (A χ : ℂ) := by
          have hh2 := hstep1 χ hχF
          rw [hs1, hadd, Work.CharCore.cfInner_add_left, hgτ, zero_add] at hh2
          rw [hh2, mul_neg, mul_one]
        have hne2 : Work.CharCore.cfInner h (τ' χ) ≠ 0 := by
          rw [hhτ]
          exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (hA1 χ hχF)))
        rcases htau_ne χ hχF h hh hne2 with hh1 | hh1
        · have h1 : Work.CharCore.cfInner h (τ' χ) = 1 := by
            rw [hh1, Work.CharCore.cfInner_self_mem_Irr hh]
          rw [h1] at hhτ
          have hre := congrArg Complex.re hhτ
          simp only [Complex.natCast_re, Complex.neg_re, Complex.one_re] at hre
          have hAle : (1:ℝ) ≤ (A χ : ℝ) := by exact_mod_cast hA1 χ hχF
          linarith
        · have h1 : Work.CharCore.cfInner h (τ' χ) = -1 := by
            rw [hh1, Work.CharCore.cfInner_neg_right, Work.CharCore.cfInner_self_mem_Irr hh]
          rw [h1] at hhτ
          have hAχ : A χ = 1 := by
            have h2 : ((A χ : ℂ)) = 1 := by
              have h3 := congrArg Neg.neg hhτ
              simpa using h3.symm
            exact_mod_cast h2
          have hdeg : (H.index : ℂ) = 2 * (Work.CharCore.irrDeg g : ℂ) := by
            have h1' := congrFun hadd 1
            rw [Work.Induction.indFun_apply_one H lam, hlam1, mul_one, Pi.add_apply] at h1'
            have hg1 : g 1 = - (τ' χ₀ 1) := by rw [hrel]; simp
            have hh1v : h 1 = - (τ' χ 1) := by rw [hh1]; simp
            rw [hg1, hh1v, hτdeg χ hχF, hAχ, Nat.cast_one, one_mul] at h1'
            have hτ01 : τ' χ₀ 1 = - (Work.CharCore.irrDeg g : ℂ) := by
              rw [hrel]; simp only [Pi.neg_apply, Work.CharCore.irrDeg_spec hg]
            rw [hτ01] at h1'
            rw [h1']; ring
          have hnat : H.index = 2 * Work.CharCore.irrDeg g := by exact_mod_cast hdeg
          exact Nat.not_even_iff_odd.mpr hHindexOdd
            ⟨Work.CharCore.irrDeg g, by rw [hnat, two_mul]⟩
    rcases hsome with hsome | hsome
    · have hr : τ' χ₀ = f₁ ∨ τ' χ₀ = -f₁ := by
        rcases hcase₀ with hc | hc
        · exact Or.inl (by rw [hc, hsome])
        · exact Or.inr (by rw [hc, hsome])
      exact contra f₁ f₂ hf1 hf2 hfne hind hr
    · have hr : τ' χ₀ = f₂ ∨ τ' χ₀ = -f₂ := by
        rcases hcase₀ with hc | hc
        · exact Or.inl (by rw [hc, hsome])
        · exact Or.inr (by rw [hc, hsome])
      exact contra f₂ f₁ hf2 hf1 (Ne.symm hfne) (by rw [hind, add_comm]) hr
  -- consequently `f₁` and `f₂` are orthogonal to every `τ' χ`, `χ ∈ S`
  have hsum0 : ∀ χ ∈ Fs, Work.CharCore.cfInner f₁ (τ' χ) + Work.CharCore.cfInner f₂ (τ' χ) = 0 := by
    intro χ hχ
    have h := hstep1 χ hχ
    rw [hs0, mul_zero] at h
    rw [hind, Work.CharCore.cfInner_add_left] at h
    exact h
  have hzero1 : ∀ χ ∈ Fs, Work.CharCore.cfInner f₁ (τ' χ) = 0 := by
    intro χ hχ
    by_contra hne1
    have hsum := hsum0 χ hχ
    have hne2 : Work.CharCore.cfInner f₂ (τ' χ) ≠ 0 := by
      intro h2; rw [h2, add_zero] at hsum; exact hne1 hsum
    have h1 := htau_ne χ hχ f₁ hf1 hne1
    have h2 := htau_ne χ hχ f₂ hf2 hne2
    rcases heq_or h1 h2 with heq | heq
    · exact hfne heq
    · exact hirr_ne_neg f₁ f₂ hf1 hf2 heq
  have hzero2 : ∀ χ ∈ Fs, Work.CharCore.cfInner f₂ (τ' χ) = 0 := by
    intro χ hχ
    have hsum := hsum0 χ hχ
    rw [hzero1 χ hχ, zero_add] at hsum
    exact hsum
  -- multiplicities of `Res f_j` on `𝒮` are proportional to the one of `χ₀`
  have hkey1 : ∀ χ ∈ Fs, Work.CharCore.cfInner (Work.Induction.resFun H f₁) χ
      = (A χ : ℂ) * Work.CharCore.cfInner (Work.Induction.resFun H f₁) χ₀ := by
    intro χ hχ
    have hrec : Work.CharCore.cfInner (Work.Induction.resFun H f₁) (χ - (A χ : ℤ) • χ₀)
        = Work.CharCore.cfInner f₁ (Work.Induction.indFun H (χ - (A χ : ℤ) • χ₀)) :=
      (hinst_eq (Work.Induction.resFun H f₁) (χ - (A χ : ℤ) • χ₀)).symm.trans
        (Work.Induction.frobenius_reciprocity_transposed H f₁ _
          (Work.CharCore.isClassFun_of_mem_Irr hf1)).symm
    have h0 : Work.CharCore.cfInner (Work.Induction.resFun H f₁) (χ - (A χ : ℤ) • χ₀) = 0 := by
      rw [hrec, hτeq χ hχ, Work.CharCore.cfInner_sub_right, hzsr,
          hzero1 χ hχ, hzero1 χ₀ hχ₀F]
      ring
    rw [Work.CharCore.cfInner_sub_right, hzsr, sub_eq_zero] at h0
    exact h0
  have hkey2 : ∀ χ ∈ Fs, Work.CharCore.cfInner (Work.Induction.resFun H f₂) χ
      = (A χ : ℂ) * Work.CharCore.cfInner (Work.Induction.resFun H f₂) χ₀ := by
    intro χ hχ
    have hrec : Work.CharCore.cfInner (Work.Induction.resFun H f₂) (χ - (A χ : ℤ) • χ₀)
        = Work.CharCore.cfInner f₂ (Work.Induction.indFun H (χ - (A χ : ℤ) • χ₀)) :=
      (hinst_eq (Work.Induction.resFun H f₂) (χ - (A χ : ℤ) • χ₀)).symm.trans
        (Work.Induction.frobenius_reciprocity_transposed H f₂ _
          (Work.CharCore.isClassFun_of_mem_Irr hf2)).symm
    have h0 : Work.CharCore.cfInner (Work.Induction.resFun H f₂) (χ - (A χ : ℤ) • χ₀) = 0 := by
      rw [hrec, hτeq χ hχ, Work.CharCore.cfInner_sub_right, hzsr,
          hzero2 χ hχ, hzero2 χ₀ hχ₀F]
      ring
    rw [Work.CharCore.cfInner_sub_right, hzsr, sub_eq_zero] at h0
    exact h0
  -- the degree count
  obtain ⟨b₁, hb₁val, hb₁ineq⟩ :=
    restriction_degree_count Fs hFirr hχ₀F A hA hf1 hkey1
  obtain ⟨b₂, hb₂val, hb₂ineq⟩ :=
    restriction_degree_count Fs hFirr hχ₀F A hA hf2 hkey2
  have hsumK : ∑ χ ∈ Fs, A χ * Work.CharCore.irrDeg χ = Nat.card S * (Nat.card Q₁ - 1) := by
    have hAdeg : ∀ χ ∈ Fs, A χ * Nat.card D = Work.CharCore.irrDeg χ := by
      intro χ hχ
      have h1 := hA χ hχ
      have h2 : ((Work.CharCore.irrDeg χ : ℂ)) = ((A χ * Nat.card D : ℕ) : ℂ) := by
        rw [← Work.CharCore.irrDeg_spec (hFirr χ hχ), h1, hχ₀deg, Nat.cast_mul]
      exact Nat.cast_injective h2.symm
    have hsq : ∑ χ ∈ Fs, (Work.CharCore.irrDeg χ) ^ 2
        = Nat.card D * (Nat.card S * (Nat.card Q₁ - 1)) := by
      apply Nat.cast_injective (R := ℝ)
      have hreal := Work.ThmG.sum_deg_sq_excludingKernel (H := H) Q₁ hQ₁H hQ₁N
      have hq1 : 1 ≤ Nat.card Q₁ := by have := Nat.card_pos (α := ↥Q₁); omega
      have hcast : ((Nat.card D * (Nat.card S * (Nat.card Q₁ - 1)) : ℕ) : ℝ)
          = (Nat.card H : ℝ) - ((Q₁.subgroupOf H).index : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hq1, hcardH, hindex, hcardQ]
        push_cast
        ring
      rw [hcast, ← hreal]
      simp only [Nat.cast_sum, Nat.cast_pow]
      rfl
    have hmul : (∑ χ ∈ Fs, A χ * Work.CharCore.irrDeg χ) * Nat.card D
        = Nat.card D * (Nat.card S * (Nat.card Q₁ - 1)) := by
      rw [Finset.sum_mul, ← hsq]
      refine Finset.sum_congr rfl (fun χ hχ => ?_)
      have h := hAdeg χ hχ
      calc A χ * Work.CharCore.irrDeg χ * Nat.card D
          = Work.CharCore.irrDeg χ * (A χ * Nat.card D) := by ring
        _ = Work.CharCore.irrDeg χ * Work.CharCore.irrDeg χ := by rw [h]
        _ = Work.CharCore.irrDeg χ ^ 2 := by ring
    have hmul' : Nat.card D * (∑ χ ∈ Fs, A χ * Work.CharCore.irrDeg χ)
        = Nat.card D * (Nat.card S * (Nat.card Q₁ - 1)) := by
      rw [Nat.mul_comm (Nat.card D) (∑ χ ∈ Fs, A χ * Work.CharCore.irrDeg χ)]
      exact hmul
    exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hDne) hmul'
  have hb₁K : b₁ * (Nat.card S * (Nat.card Q₁ - 1)) ≤ Work.CharCore.irrDeg f₁ := by
    rw [hsumK] at hb₁ineq; exact hb₁ineq
  have hb₂K : b₂ * (Nat.card S * (Nat.card Q₁ - 1)) ≤ Work.CharCore.irrDeg f₂ := by
    rw [hsumK] at hb₂ineq; exact hb₂ineq
  have hdegsum : Work.CharCore.irrDeg f₁ + Work.CharCore.irrDeg f₂ = H.index := by
    have h := congrFun hind 1
    rw [Work.Induction.indFun_apply_one H lam, hlam1, mul_one, Pi.add_apply] at h
    rw [Work.CharCore.irrDeg_spec hf1, Work.CharCore.irrDeg_spec hf2] at h
    have h2 : ((Work.CharCore.irrDeg f₁ + Work.CharCore.irrDeg f₂ : ℕ) : ℂ) = (H.index : ℂ) := by
      rw [Nat.cast_add]; exact h.symm
    exact Nat.cast_injective h2
  have harith : (b₁ + b₂) * (Nat.card S * (Nat.card Q₁ - 1)) ≤ Nat.card Q + 1 := by
    have h1 : b₁ * (Nat.card S * (Nat.card Q₁ - 1)) + b₂ * (Nat.card S * (Nat.card Q₁ - 1))
        ≤ Work.CharCore.irrDeg f₁ + Work.CharCore.irrDeg f₂ := Nat.add_le_add hb₁K hb₂K
    rw [hdegsum, hindexQ, ← add_mul] at h1
    exact h1
  have hb12 : b₁ + b₂ ≤ 1 := by
    by_contra hcon
    have h2 : 2 ≤ b₁ + b₂ := by omega
    have h4 : 2 * (Nat.card S * (Nat.card Q₁ - 1)) ≤ Nat.card S * Nat.card Q₁ + 1 := by
      have h := harith
      rw [hcardQ] at h
      exact le_trans (Nat.mul_le_mul_right _ h2) h
    have hY : Nat.card S * Nat.card Q₁ ≤ Nat.card S * (Nat.card Q₁ - 1) + Nat.card S := by
      have hq : Nat.card Q₁ - 1 + 1 = Nat.card Q₁ :=
        Nat.sub_add_cancel (by omega : 1 ≤ Nat.card Q₁)
      conv_lhs => rw [← hq]
      rw [Nat.mul_add, Nat.mul_one]
    have h5 : Nat.card S * (Nat.card Q₁ - 1) ≤ Nat.card S + 1 := by omega
    have h6 : 2 * Nat.card S ≤ Nat.card S * (Nat.card Q₁ - 1) := by
      have hqq : 2 ≤ Nat.card Q₁ - 1 := by omega
      calc 2 * Nat.card S = Nat.card S * 2 := by ring
        _ ≤ Nat.card S * (Nat.card Q₁ - 1) := Nat.mul_le_mul_left _ hqq
    omega
  -- the principal character is orthogonal to `Ind λ`
  have hpri : (fun _ : G => (1 : ℂ)) ∈ Work.CharCore.Irr G :=
    Work.CharCore.principalChar_mem_Irr
  have hpriH : (fun _ : ↥H => (1 : ℂ)) ∈ Work.CharCore.Irr ↥H :=
    Work.CharCore.principalChar_mem_Irr
  have hInd0 : Work.CharCore.cfInner (Work.Induction.indFun H lam) (fun _ : G => (1 : ℂ)) = 0 := by
    have hrec : Work.CharCore.cfInner (Work.Induction.indFun H lam) (fun _ : G => (1 : ℂ))
        = Work.CharCore.cfInner lam (Work.Induction.resFun H (fun _ : G => (1 : ℂ))) :=
      (Work.Induction.frobenius_reciprocity H lam _ (Work.CharCore.isClassFun_const 1)).trans
        (hinst_eq lam _)
    rw [hrec]
    have hres : Work.Induction.resFun H (fun _ : G => (1 : ℂ)) = (fun _ : ↥H => (1 : ℂ)) := rfl
    rw [hres, Work.CharCore.irr_orthonormal lam _ hlam hpriH, if_neg hlamne]
  have hne_of' : ∀ g : G → ℂ, g ∈ Work.CharCore.Irr G →
      Work.CharCore.cfInner g (fun _ : G => (1 : ℂ)) = 0 → g ≠ (fun _ : G => (1 : ℂ)) := by
    intro g hg h0 hcon
    have h1 : Work.CharCore.cfInner (fun _ : G => (1 : ℂ)) (fun _ : G => (1 : ℂ)) = 1 :=
      Work.CharCore.cfInner_self_mem_Irr hpri
    rw [hcon] at h0
    rw [h1] at h0
    exact one_ne_zero h0
  have hf1ne : f₁ ≠ (fun _ : G => (1 : ℂ)) := by
    apply hne_of' f₁ hf1
    have h12 : Work.CharCore.cfInner f₁ (fun _ : G => (1 : ℂ))
        + Work.CharCore.cfInner f₂ (fun _ : G => (1 : ℂ)) = 0 := by
      rw [← Work.CharCore.cfInner_add_left, ← hind]
      exact hInd0
    rw [Work.CharCore.irr_orthonormal f₁ _ hf1 hpri]
    by_cases h1 : f₁ = (fun _ : G => (1 : ℂ))
    · rw [if_pos h1]
      rw [Work.CharCore.irr_orthonormal f₁ _ hf1 hpri, if_pos h1] at h12
      by_cases h2 : f₂ = (fun _ : G => (1 : ℂ))
      · rw [Work.CharCore.irr_orthonormal f₂ _ hf2 hpri, if_pos h2] at h12
        exact absurd h12 (by norm_num)
      · rw [Work.CharCore.irr_orthonormal f₂ _ hf2 hpri, if_neg h2] at h12
        exact absurd h12 (by norm_num)
    · rw [if_neg h1]
  have hf2ne : f₂ ≠ (fun _ : G => (1 : ℂ)) := by
    apply hne_of' f₂ hf2
    have h12 : Work.CharCore.cfInner f₁ (fun _ : G => (1 : ℂ))
        + Work.CharCore.cfInner f₂ (fun _ : G => (1 : ℂ)) = 0 := by
      rw [← Work.CharCore.cfInner_add_left, ← hind]
      exact hInd0
    rw [Work.CharCore.irr_orthonormal f₂ _ hf2 hpri]
    by_cases h2 : f₂ = (fun _ : G => (1 : ℂ))
    · rw [if_pos h2]
      rw [Work.CharCore.irr_orthonormal f₂ _ hf2 hpri, if_pos h2] at h12
      by_cases h1 : f₁ = (fun _ : G => (1 : ℂ))
      · rw [Work.CharCore.irr_orthonormal f₁ _ hf1 hpri, if_pos h1] at h12
        exact absurd h12 (by norm_num)
      · rw [Work.CharCore.irr_orthonormal f₁ _ hf1 hpri, if_neg h1] at h12
        exact absurd h12 (by norm_num)
    · rw [if_neg h2]
  -- conclusion
  have hb01 : b₁ = 0 ∨ b₂ = 0 := by omega
  rcases hb01 with hb | hb
  · refine ⟨f₁, hf1, hf1ne, ?_⟩
    apply trivial_on_Q1_of_orthogonal hf1
    intro χ hχ
    rw [hkey1 χ hχ, hb₁val, hb, Nat.cast_zero, mul_zero]
  · refine ⟨f₂, hf2, hf2ne, ?_⟩
    apply trivial_on_Q1_of_orthogonal hf2
    intro χ hχ
    rw [hkey2 χ hχ, hb₂val, hb, Nat.cast_zero, mul_zero]

end Work.ThmG
