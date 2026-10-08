import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.CharCore.Main
import Submission.Work.Induction.All
import Submission.Work.Induction.TwoDoubleCosetSetup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausTwoGroup

noncomputable section

open Classical

/-- If a non-identity element of a subgroup is not `1`, its image in the ambient group is not
`1` either. -/
theorem coe_ne_one {G : Type} [Group G] {Q : Subgroup G} {x : ↥Q} (hx : x ≠ 1) :
    (x : G) ≠ 1 := by
  intro h
  exact hx (Subtype.ext h)

/-! ## Auxiliary character-theory lemmas

These are the pieces of the proof of `good_is_constituent` below. -/

/-- Row orthogonality against the principal character: a non-trivial irreducible character of a
finite group has value sum `0`. -/
theorem sum_irr_eq_zero_of_ne_one {K : Type} [Group K] [Fintype K]
    {ζ : K → ℂ} (hζ : ζ ∈ Work.CharCore.Irr K) (hζ1 : ζ ≠ 1) :
    ∑ x : K, ζ x = 0 := by
  have h := Work.CharCore.irr_orthonormal ζ (fun _ : K => (1 : ℂ)) hζ
    Work.CharCore.principalChar_mem_Irr
  rw [Work.CharCore.cfInner_apply] at h
  have hone : (fun _ : K => (1 : ℂ)) = (1 : K → ℂ) := rfl
  rw [hone, if_neg hζ1] at h
  simp only [map_one, mul_one] at h
  have hcard : ((Fintype.card K : ℂ))⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
  exact (mul_eq_zero.mp h).resolve_left hcard

/-- The kernel of a non-trivial irreducible character of a finite simple group is trivial. -/
theorem irrKer_eq_bot_of_isSimpleGroup {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    {χ : G → ℂ} (hχ : χ ∈ Work.CharCore.Irr G) (hχ1 : χ ≠ 1) :
    Work.CharCore.irrKer χ hχ = ⊥ := by
  rcases (haveI := Work.CharCore.irrKer_normal χ hχ
    Subgroup.Normal.eq_bot_or_eq_top (Work.CharCore.irrKer χ hχ)) with h | h
  · exact h
  · exfalso
    have hconst : ∀ g : G, χ g = χ 1 := by
      intro g
      have : g ∈ Work.CharCore.irrKer χ hχ := by rw [h]; exact Subgroup.mem_top g
      exact (Work.CharCore.mem_irrKer hχ).mp this
    have h0 : Work.CharCore.cfInner χ (fun _ : G => (1 : ℂ)) = 0 := by
      have hh := Work.CharCore.irr_orthonormal χ (fun _ : G => (1 : ℂ)) hχ
        Work.CharCore.principalChar_mem_Irr
      have hone : (fun _ : G => (1 : ℂ)) = (1 : G → ℂ) := rfl
      rw [hone, if_neg hχ1] at hh
      exact hh
    have h1 : Work.CharCore.cfInner χ (fun _ : G => (1 : ℂ)) = χ 1 := by
      rw [Work.CharCore.cfInner_apply]
      simp only [map_one, mul_one]
      rw [Finset.sum_congr rfl (fun x _ => hconst x)]
      simp [Finset.card_univ, nsmul_eq_mul]
    rw [h0] at h1
    have hspec := Work.CharCore.irrDeg_spec hχ
    have hpos := Work.CharCore.irrDeg_pos hχ
    rw [hspec] at h1
    exact hpos.ne' (Nat.cast_eq_zero.mp h1.symm)

/-- If a function `f` on a finite group is constantly `c` off the identity and `ζ` is a
non-trivial irreducible character with `ζ 1 = 1`, then `⟪f, ζ⟫ = |K|⁻¹ (f 1 - c)`. -/
theorem cfInner_eq_inv_card_mul_of_const_off_one {K : Type} [Group K] [Fintype K]
    {f ζ : K → ℂ} {c : ℂ}
    (hf : ∀ x : K, x ≠ 1 → f x = c)
    (hζ : ζ ∈ Work.CharCore.Irr K) (hζ1 : ζ ≠ 1) (hζone : ζ 1 = 1) :
    Work.CharCore.cfInner f ζ = (Fintype.card K : ℂ)⁻¹ * (f 1 - c) := by
  classical
  rw [Work.CharCore.cfInner_apply]
  congr 1
  have hsplit : ∑ x : K, f x * starRingEnd ℂ (ζ x)
      = f 1 * starRingEnd ℂ (ζ 1)
        + ∑ x ∈ Finset.univ.erase (1 : K), f x * starRingEnd ℂ (ζ x) := by
    rw [← Finset.sum_erase_add Finset.univ
      (fun x => f x * starRingEnd ℂ (ζ x)) (Finset.mem_univ 1)]
    ring
  rw [hsplit]
  have herase : ∑ x ∈ Finset.univ.erase (1 : K), starRingEnd ℂ (ζ x) = -1 := by
    have h1 : (∑ x ∈ Finset.univ.erase (1 : K), ζ x) + ζ 1 = ∑ x : K, ζ x :=
      Finset.sum_erase_add Finset.univ ζ (Finset.mem_univ 1)
    rw [sum_irr_eq_zero_of_ne_one hζ hζ1, hζone, add_eq_zero_iff_eq_neg] at h1
    calc ∑ x ∈ Finset.univ.erase (1 : K), starRingEnd ℂ (ζ x)
        = starRingEnd ℂ (∑ x ∈ Finset.univ.erase (1 : K), ζ x) := by rw [map_sum]
      _ = starRingEnd ℂ (-1) := by rw [h1]
      _ = -1 := by simp
  have hc' : ∑ x ∈ Finset.univ.erase (1 : K), f x * starRingEnd ℂ (ζ x)
      = c * ∑ x ∈ Finset.univ.erase (1 : K), starRingEnd ℂ (ζ x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.mem_erase] at hx
    rw [hf x hx.1]
  rw [hc', herase, hζone, map_one, mul_one]
  ring

/-! ## The main lemma -/

theorem good_is_constituent {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    {H Q : Subgroup G} [Fintype ↥Q] {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    {ζ₁ : ↥Q → ℂ} (hζ : ζ₁ ∈ Work.CharCore.Irr ↥Q) (hζ1 : ζ₁ ≠ 1) (hlin : ζ₁ 1 = 1)
    {χ₀ : (↥Q → ℂ) → G → ℂ}
    (hχconst : ∀ φ ∈ Work.CharCore.Irr G, (∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → φ ≠ χ₀ ζ) →
      ∀ y : G, y ∈ Q → y ≠ 1 → ∀ y' : G, y' ∈ Q → y' ≠ 1 → φ y = φ y')
    {ψ : G → ℂ} (hψ : ψ ∈ Work.CharCore.Irr G) (hψ1 : ψ ≠ 1)
    (hψexc : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ψ ≠ χ₀ ζ) :
    Work.CharCore.cfInner ψ (Work.Induction.indFun Q ζ₁) ≠ 0 := by
  classical
  -- `Q` is non-trivial, because `ζ₁ ≠ 1` is a non-trivial linear character of `↥Q`.
  have hQne : Q ≠ ⊥ := by
    intro hbot
    apply hζ1
    funext x
    have hx : (x : G) = 1 := by
      have hxmem : (x : G) ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact x.2
      simpa using hxmem
    have hx1 : x = 1 := Subtype.ext hx
    show ζ₁ x = 1
    rw [hx1]
    exact hlin
  obtain ⟨y₀, hy₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQne
  have hy₀G : (y₀ : G) ≠ 1 := fun hh => hy₀ (Subtype.ext hh)
  set c : ℂ := ψ (y₀ : G) with hcdef
  have hconst := hχconst ψ hψ hψexc
  -- The non-exceptional character `ψ` is constant on `Q ∖ {1}` with value `c`; we need
  -- `ψ 1 ≠ c`.
  have hne : ψ 1 ≠ c := by
    intro hψ1c
    have hle : Q ≤ Work.CharCore.irrKer ψ hψ := by
      intro x hxQ
      rw [Work.CharCore.mem_irrKer]
      by_cases hx1 : x = 1
      · rw [hx1]
      · have hxy : ψ x = ψ (y₀ : G) := hconst x hxQ hx1 (y₀ : G) y₀.2 hy₀G
        rw [hxy, ← hcdef, hψ1c]
    have hirr := irrKer_eq_bot_of_isSimpleGroup hψ hψ1
    have hQle : Q ≤ (⊥ : Subgroup G) := by rw [← hirr]; exact hle
    exact hQne (le_bot_iff.mp hQle)
  -- The restriction of `ψ` to `Q` is constant `c` off the identity, and `ψ 1 ≠ c`.
  have hcf : Work.CharCore.cfInner (Work.Induction.resFun Q ψ) ζ₁
      = (Fintype.card ↥Q : ℂ)⁻¹ * (ψ 1 - c) := by
    have hf : ∀ x : ↥Q, x ≠ 1 → (Work.Induction.resFun Q ψ) x = c := by
      intro x hx1
      have hxG : (x : G) ≠ 1 := coe_ne_one hx1
      show ψ (x : G) = c
      rw [hconst (x : G) x.2 hxG (y₀ : G) y₀.2 hy₀G]
    have hmain := cfInner_eq_inv_card_mul_of_const_off_one hf hζ hζ1 hlin
    have hres1 : (Work.Induction.resFun Q ψ) (1 : ↥Q) = ψ 1 := rfl
    rwa [hres1] at hmain
  have hcfne : Work.CharCore.cfInner (Work.Induction.resFun Q ψ) ζ₁ ≠ 0 := by
    rw [hcf]
    exact mul_ne_zero (inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero))
      (sub_ne_zero.mpr hne)
  -- Frobenius reciprocity `⟨ψ, Ind_Q^G ζ₁⟩ = ⟨Res_Q ψ, ζ₁⟩`, using the `Fintype ↥Q` instance
  -- carried by the hypotheses (`frobenius_reciprocity_local`).
  have hfr : Work.CharCore.cfInner ψ (Work.Induction.indFun Q ζ₁)
      = Work.CharCore.cfInner (Work.Induction.resFun Q ψ) ζ₁ := by
    rw [Work.CharCore.cfInner_conj_symm ψ (Work.Induction.indFun Q ζ₁),
      Work.Induction.frobenius_reciprocity_local Q ζ₁ ψ (Work.CharCore.isClassFun_of_mem_Irr hψ),
      ← Work.CharCore.cfInner_conj_symm (Work.Induction.resFun Q ψ) ζ₁]
  rw [hfr]
  exact hcfne

end

end Work.ZassenhausTwoGroup
