import Mathlib
import Submission.Work.CharCore.Main
import Submission.Work.Clifford.irr_precomp_mulEquiv
import Submission.Work.Clifford.clifford_correspondence
import Submission.Work.Clifford.CoherenceBridge
import Submission.Work.Frobenius.Induced.irr_eq_one_of_fpf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.CharQ.orbit_two_irr`

Let `K` be a finite group carrying a fixed-point-free action of a finite group `A` of odd order
(`ρ : A →* MulAut K`, only `1` fixed by every `a ≠ 1`), and suppose `K` is not a `2`-group.  Then
there are two non-trivial irreducible characters `θ₁, θ₂` of `K` which are *not* conjugate under
the action, i.e. `θ₂` is not of the form `x ↦ θ₁ (ρ a x)`.
-/

noncomputable section

open Classical

namespace Work.FeitSibley.CharQ

variable {K : Type} [Group K] [Fintype K]

/-- The principal (trivial) character `K → ℂ`. -/
private abbrev principal (K : Type) : K → ℂ := fun _ => 1

/-- The degree of the principal character is `1`. -/
private theorem irrDeg_principal : Work.CharCore.irrDeg (principal K) = 1 := by
  apply Nat.cast_injective (R := ℂ)
  rw [← Work.CharCore.irrDeg_spec (Work.CharCore.principalChar_mem_Irr (G := K))]
  norm_num [principal]

/-- An irreducible character which is constant (i.e. takes only the value `θ 1`) is principal. -/
private theorem eq_principal_of_forall_eq_one {θ : K → ℂ} (hθ : θ ∈ Work.CharCore.Irr K)
    (h : ∀ x : K, θ x = θ 1) : θ = principal K := by
  have hconst : θ = (θ 1) • principal K := by
    funext x
    simpa only [Pi.smul_apply, principal, Pi.one_apply, smul_eq_mul, mul_one] using h x
  have hc : Work.CharCore.cfInner θ (principal K)
      = if θ = principal K then 1 else 0 :=
    Work.CharCore.irr_orthonormal θ _ hθ (Work.CharCore.principalChar_mem_Irr (G := K))
  have hc2 : Work.CharCore.cfInner θ (principal K) = θ 1 := by
    conv_lhs => rw [hconst]
    rw [Work.CharCore.cfInner_smul_left]
    rw [Work.CharCore.irr_orthonormal _ _ (Work.CharCore.principalChar_mem_Irr (G := K))
      (Work.CharCore.principalChar_mem_Irr (G := K)), if_pos rfl, mul_one]
  rw [hc2] at hc
  by_cases hpr : θ = principal K
  · exact hpr
  · rw [if_neg hpr] at hc
    have hne : (Work.CharCore.irrDeg θ : ℂ) ≠ 0 := Work.CharCore.irrDeg_ne_zero hθ
    rw [Work.CharCore.irrDeg_spec hθ] at hc
    exact absurd hc hne

/-- A non-trivial finite group has a non-constant irreducible character. -/
private theorem exists_nontrivial_irr (h1 : Nat.card K ≠ 1) :
    ∃ θ ∈ Work.CharCore.Irr K, ∃ x : K, θ x ≠ θ 1 := by
  by_contra hcon
  push_neg at hcon
  have hsingle : Work.CharCore.Irr K = {principal K} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨Work.CharCore.principalChar_mem_Irr (G := K), ?_⟩
    intro x hx
    exact eq_principal_of_forall_eq_one hx (hcon x hx)
  have hsum := Work.CharCore.sum_irr_degree_sq (G := K)
  rw [hsingle, Finset.sum_singleton] at hsum
  have hcast : (Nat.card K : ℂ) = ((1 : ℕ) : ℂ) := by rw [← hsum]; norm_num [principal]
  exact h1 (Nat.cast_injective hcast)

/-- An element of order `≠ 2` exists as soon as `K` is not a `2`-group. -/
private theorem exists_orderOf_ne_two (hnot2 : ¬ IsPGroup 2 K) :
    ∃ y : K, y ≠ 1 ∧ orderOf y ≠ 2 := by
  unfold IsPGroup at hnot2
  push_neg at hnot2
  obtain ⟨g, hg⟩ := hnot2
  refine ⟨g, ?_, ?_⟩
  · intro h; exact hg 0 (by rw [h]; simp)
  · intro h
    exact hg 1 (by rw [show (2 : ℕ) ^ 1 = 2 from by norm_num, ← h]; exact pow_orderOf_eq_one g)

theorem orbit_two_irr {A : Type} [Group A] [Fintype A] (ρ : A →* MulAut K)
    (hodd : Odd (Nat.card A))
    (hfpf : ∀ a : A, a ≠ 1 → ∀ x : K, ρ a x = x → x = 1)
    (hnot2 : ¬ IsPGroup 2 K) :
    ∃ θ₁ ∈ Work.CharCore.Irr K, ∃ θ₂ ∈ Work.CharCore.Irr K,
      (∃ x : K, θ₁ x ≠ θ₁ 1) ∧ (∃ x : K, θ₂ x ≠ θ₂ 1) ∧
      (∀ a : A, (fun x => θ₁ (ρ a x)) ≠ θ₂) := by
  classical
  have hcard1 : Nat.card K ≠ 1 := by
    intro h1
    exact hnot2 (IsPGroup.iff_card.mpr ⟨0, by rw [h1]; norm_num⟩)
  obtain ⟨θ₀, hθ₀, hn₀⟩ := exists_nontrivial_irr hcard1
  have hθ₀C : θ₀ ∈ Work.Clifford.Irr K := (Work.Clifford.corr_mem_Irr_charCore (G := K)).mpr hθ₀
  have hθ₀F : θ₀ ∈ Work.Frobenius.Irr K :=
    (Work.Frobenius.Bridge.mem_Irr_iff_coherence).mpr
      ((Work.CharCore.mem_Irr_iff_coherence (G := K)).mp hθ₀)
  by_contra hcon
  have hcon' : ∀ θ₁ ∈ Work.CharCore.Irr K, ∀ θ₂ ∈ Work.CharCore.Irr K,
      (∃ x : K, θ₁ x ≠ θ₁ 1) → (∃ x : K, θ₂ x ≠ θ₂ 1) →
      ∃ a : A, (fun x : K => θ₁ (ρ a x)) = θ₂ := by
    intro θ₁ h₁ θ₂ h₂ hn₁ hn₂
    by_contra hh
    push_neg at hh
    exact hcon ⟨θ₁, h₁, θ₂, h₂, hn₁, hn₂, hh⟩
  -- the orbit map is injective
  have hinj : Function.Injective (fun a : A => (fun x : K => θ₀ (ρ a x))) := by
    intro a b hab
    have hfix : ∀ x : K, θ₀ (ρ (a * b⁻¹) x) = θ₀ x := by
      intro x
      have h1 : ρ (a * b⁻¹) x = (ρ a) ((ρ b⁻¹) x) := by
        rw [map_mul]; rfl
      rw [h1]
      have h2 : (ρ b) ((ρ b⁻¹) x) = x := by
        rw [map_inv]
        have h3 : ρ b * (ρ b)⁻¹ = 1 := mul_inv_cancel (ρ b)
        have h4 : (ρ b * (ρ b)⁻¹) x = (1 : MulAut K) x := by rw [h3]
        rwa [MulAut.mul_apply, MulAut.one_apply] at h4
      exact (congrFun hab ((ρ b⁻¹) x)).trans (congrArg θ₀ h2)
    by_contra hne
    have hc : a * b⁻¹ ≠ 1 := fun h => hne (by
      calc a = (a * b⁻¹) * b := by group
        _ = 1 * b := by rw [h]
        _ = b := by simp)
    have hprinc :=
      Work.Frobenius.Induced.irr_eq_one_of_fpf (ρ (a * b⁻¹)) (hfpf _ hc) hθ₀F hfix
    obtain ⟨x, hx⟩ := hn₀
    exact hx (by simp [hprinc])
  -- the set `S` of non-trivial irreducibles is the orbit of `θ₀`
  set S : Finset (K → ℂ) := (Work.CharCore.Irr K).filter (fun θ => ∃ x : K, θ x ≠ θ 1)
    with hSdef
  have hSimg : S = Finset.univ.image (fun a : A => (fun x : K => θ₀ (ρ a x))) := by
    apply Finset.ext
    intro θ
    rw [hSdef]
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hθ, hnθ⟩
      exact hcon' θ₀ hθ₀ θ hθ hn₀ hnθ
    · rintro ⟨a, rfl⟩
      refine ⟨?_, ?_⟩
      · exact (Work.Clifford.corr_mem_Irr_charCore (G := K)).mp
          (Work.Clifford.irr_precomp_mulEquiv (ρ a) hθ₀C)
      · obtain ⟨x, hx⟩ := hn₀
        refine ⟨(ρ a)⁻¹ x, ?_⟩
        have h1 : (ρ a) ((ρ a)⁻¹ x) = x := by
          have h3 : ρ a * (ρ a)⁻¹ = 1 := mul_inv_cancel (ρ a)
          have h4 : (ρ a * (ρ a)⁻¹) x = (1 : MulAut K) x := by rw [h3]
          rwa [MulAut.mul_apply, MulAut.one_apply] at h4
        show θ₀ ((ρ a) ((ρ a)⁻¹ x)) ≠ θ₀ ((ρ a) 1)
        rw [h1, map_one]
        exact hx
  have hScard : S.card = Nat.card A := by
    rw [hSimg, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_eq_nat_card]
  have hdegSnat : ∀ θ ∈ S, Work.CharCore.irrDeg θ = Work.CharCore.irrDeg θ₀ := by
    intro θ hθS
    rw [hSdef, Finset.mem_filter] at hθS
    obtain ⟨hθIrr, hnθ⟩ := hθS
    obtain ⟨a, ha⟩ := hcon' θ₀ hθ₀ θ hθIrr hn₀ hnθ
    apply Nat.cast_injective (R := ℂ)
    rw [← Work.CharCore.irrDeg_spec hθIrr, ← Work.CharCore.irrDeg_spec hθ₀, ← ha]
    simp
  have hcompl : (Work.CharCore.Irr K).filter (fun θ => ¬ ∃ x : K, θ x ≠ θ 1)
      = {principal K} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Work.CharCore.principalChar_mem_Irr (G := K),
        by rintro ⟨x, hx⟩; exact hx rfl⟩
    · intro θ hθ
      rw [Finset.mem_filter] at hθ
      exact eq_principal_of_forall_eq_one hθ.1 (fun x => by
        by_contra hne
        exact hθ.2 ⟨x, hne⟩)
  have hsumNat : ∑ θ ∈ Work.CharCore.Irr K, (Work.CharCore.irrDeg θ) ^ 2 = Nat.card K := by
    apply Nat.cast_injective (R := ℂ)
    have hcongr : ∀ θ ∈ Work.CharCore.Irr K,
        ((Work.CharCore.irrDeg θ : ℂ)) ^ 2 = θ 1 ^ 2 := by
      intro θ hθ; rw [Work.CharCore.irrDeg_spec hθ]
    rw [Nat.cast_sum]
    simp only [Nat.cast_pow]
    rw [Finset.sum_congr rfl hcongr]
    exact Work.CharCore.sum_irr_degree_sq (G := K)
  have hSsum : (∑ θ ∈ S, (Work.CharCore.irrDeg θ) ^ 2)
      = S.card * (Work.CharCore.irrDeg θ₀) ^ 2 := by
    rw [Finset.sum_congr rfl (fun θ hθ => by rw [hdegSnat θ hθ]), Finset.sum_const, smul_eq_mul]
  have hCsum : (∑ θ ∈ (Work.CharCore.Irr K).filter (fun θ => ¬ ∃ x : K, θ x ≠ θ 1),
      (Work.CharCore.irrDeg θ) ^ 2) = 1 := by
    rw [hcompl, Finset.sum_singleton, irrDeg_principal]; norm_num
  have hmain : Nat.card K = 1 + S.card * (Work.CharCore.irrDeg θ₀) ^ 2 := by
    rw [← hsumNat]
    have hsplit := Finset.sum_filter_add_sum_filter_not (Work.CharCore.Irr K)
      (fun θ : K → ℂ => ∃ x : K, θ x ≠ θ 1) (fun θ => (Work.CharCore.irrDeg θ) ^ 2)
    rw [← hsplit, ← hSdef, hSsum, hCsum]
    omega
  -- the degree is `1`
  have hK' : Nat.card K = 1 + Nat.card A * (Work.CharCore.irrDeg θ₀) ^ 2 := by
    rw [← hScard]; exact hmain
  have hδdvd : Work.CharCore.irrDeg θ₀ ∣ Nat.card K := by
    obtain ⟨d, hd1, hd2⟩ := Work.CharCore.irr_degree_dvd hθ₀
    have hd : d = Work.CharCore.irrDeg θ₀ := by
      apply Nat.cast_injective (R := ℂ)
      rw [← hd1, Work.CharCore.irrDeg_spec hθ₀]
    rwa [hd] at hd2
  have hδ1 : Work.CharCore.irrDeg θ₀ = 1 := by
    have hδdvd1 : Work.CharCore.irrDeg θ₀ ∣ Nat.card K - 1 := by
      have hK1 : Nat.card K - 1 = Nat.card A * (Work.CharCore.irrDeg θ₀) ^ 2 := by
        rw [hK']; omega
      rw [hK1]
      exact dvd_mul_of_dvd_right (dvd_pow_self _ (by norm_num)) _
    have hdiff : Work.CharCore.irrDeg θ₀ ∣ Nat.card K - (Nat.card K - 1) :=
      Nat.dvd_sub hδdvd hδdvd1
    haveI : Nonempty K := ⟨1⟩
    have hKpos : 1 ≤ Nat.card K := Nat.card_pos
    have h1 : Nat.card K - (Nat.card K - 1) = 1 := by omega
    rw [h1] at hdiff
    exact Nat.dvd_one.mp hdiff
  have hdeg1 : ∀ θ ∈ Work.CharCore.Irr K, Work.CharCore.irrDeg θ = 1 := by
    intro θ hθ
    by_cases hnθ : ∃ x : K, θ x ≠ θ 1
    · have hθS : θ ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨hθ, hnθ⟩
      rw [hdegSnat θ hθS, hδ1]
    · have hprincipal : θ = principal K := eq_principal_of_forall_eq_one hθ (fun x => by
        by_contra hne
        exact hnθ ⟨x, hne⟩)
      rw [hprincipal, irrDeg_principal]
  have hcardIrr : (Work.CharCore.Irr K).card = Nat.card K := by
    have h := hsumNat
    have hcongr : ∀ θ ∈ Work.CharCore.Irr K, (Work.CharCore.irrDeg θ) ^ 2 = (1 : ℕ) := by
      intro θ hθ; rw [hdeg1 θ hθ]; norm_num
    rw [Finset.sum_congr rfl hcongr] at h
    rw [Finset.sum_const, smul_eq_mul, mul_one] at h
    exact h
  have hScompl : S.card + 1 = (Work.CharCore.Irr K).card := by
    have h := Finset.card_filter_add_card_filter_not (s := Work.CharCore.Irr K)
      (p := fun θ : K → ℂ => ∃ x : K, θ x ≠ θ 1)
    rw [hcompl] at h
    simp only [Finset.card_singleton] at h
    simpa [hSdef] using h
  have hAK : Nat.card K = Nat.card A + 1 := by
    have h1 : S.card = Nat.card A := hScard
    have h2 : S.card + 1 = (Work.CharCore.Irr K).card := hScompl
    have h3 : (Work.CharCore.Irr K).card = Nat.card K := hcardIrr
    omega
  -- contradiction via the action on `K ∖ {1}`
  obtain ⟨y, hy1, hyord⟩ := exists_orderOf_ne_two hnot2
  have hEven : 2 ∣ Nat.card K := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + 1, by omega⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card (G := K) 2
    (by rw [Fintype.card_eq_nat_card]; exact hEven)
  have hz1 : z ≠ 1 := by intro h; rw [h] at hz; simp at hz
  have horb_inj : Function.Injective (fun a : A => ρ a z) := by
    intro a b hab
    by_contra hne
    have hc : b⁻¹ * a ≠ 1 := fun h => hne (by
      calc a = b * (b⁻¹ * a) := by group
        _ = b * 1 := by rw [h]
        _ = b := by simp)
    have hfix : ρ (b⁻¹ * a) z = z := by
      have hab' : (ρ a) z = (ρ b) z := hab
      have h1 : ρ (b⁻¹ * a) = (ρ b)⁻¹ * ρ a := by rw [map_mul, map_inv]
      rw [h1, MulAut.mul_apply, hab']
      have h3 : (ρ b)⁻¹ * ρ b = 1 := inv_mul_cancel (ρ b)
      have h4 : ((ρ b)⁻¹ * ρ b) z = (1 : MulAut K) z := by rw [h3]
      rwa [MulAut.mul_apply, MulAut.one_apply] at h4
    exact hz1 (hfpf (b⁻¹ * a) hc z hfix)
  have horb_card : (Finset.univ.image (fun a : A => ρ a z)).card = Nat.card A := by
    rw [Finset.card_image_of_injective _ horb_inj, Finset.card_univ, Fintype.card_eq_nat_card]
  have hsub : (Finset.univ.image (fun a : A => ρ a z)) ⊆ (Finset.univ : Finset K).erase 1 := by
    intro w hw
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
    obtain ⟨a, rfl⟩ := hw
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h
    have h3 : (ρ a)⁻¹ * ρ a = 1 := inv_mul_cancel (ρ a)
    have h4 : ((ρ a)⁻¹ * ρ a) z = (1 : MulAut K) z := by rw [h3]
    rw [MulAut.mul_apply, h, map_one, MulAut.one_apply] at h4
    exact hz1 h4.symm
  have horb_eq : (Finset.univ.image (fun a : A => ρ a z)) = (Finset.univ : Finset K).erase 1 := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [horb_card, Finset.card_erase_of_mem (Finset.mem_univ (1 : K)), Finset.card_univ,
      Fintype.card_eq_nat_card]
    omega
  have hy_mem : y ∈ (Finset.univ : Finset K).erase 1 := by
    rw [Finset.mem_erase]; exact ⟨hy1, Finset.mem_univ y⟩
  rw [← horb_eq, Finset.mem_image] at hy_mem
  obtain ⟨a, -, ha⟩ := hy_mem
  exact hyord (by rw [← ha, MulEquiv.orderOf_eq (ρ a) z, hz])

end Work.FeitSibley.CharQ
