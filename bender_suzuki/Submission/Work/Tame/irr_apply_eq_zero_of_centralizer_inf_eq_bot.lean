import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.CharCore.column_orthogonality_conj
import Submission.Work.Clifford.gallagher_mul_inflate_irr
import Submission.Work.Clifford.FunAPI

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

/-- **Feit–Thompson Lemma 4.3** (p. 783): let `H ⊴ G` and let `λ` be an irreducible character of
`G` which does not contain `H` in its kernel (written here as `∃ h ∈ H, λ h ≠ λ 1`).  If
`C_G(x) ∩ H = 1`, then `λ x = 0`.

(Feit–Thompson's proof: column orthogonality in `G` and in `G/H` gives
`Σ_{λ ∈ Irr G} |λ(x)|² = |C_G(x)|` and `Σ_{μ ∈ Irr G/H} |μ(x̄)|² = |C_{G/H}(x̄)|`, and
`C_G(x) → C_{G/H}(x̄)` is injective when `C_G(x) ∩ H = 1`.) -/
theorem irr_apply_eq_zero_of_centralizer_inf_eq_bot {G : Type*} [Group G] [Fintype G]
    {H : Subgroup G} (hH : H.Normal) {lam : G → ℂ} (hlam : lam ∈ CharCore.Irr G)
    (hk : ∃ h : G, h ∈ H ∧ lam h ≠ lam 1) {x : G}
    (hx : Subgroup.centralizer ({x} : Set G) ⊓ H = ⊥) : lam x = 0 := by
  classical
  -- The class of `x` in `G ⧸ H`.
  set xq : G ⧸ H := QuotientGroup.mk x with hxq
  -- ## Column orthogonality in `G`
  have hcolG := CharCore.column_orthogonality_conj (G := G) (g := x) (h := x) (IsConj.refl x)
  have hAG : (∑ χ ∈ CharCore.Irr G, Complex.normSq (χ x)) =
      ((Nat.card (Subgroup.centralizer ({x} : Set G)) : ℕ) : ℝ) := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_natCast, ← hcolG]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Complex.mul_conj]
  -- ## Column orthogonality in `G ⧸ H`
  have hcolQ := CharCore.column_orthogonality_conj (G := G ⧸ H) (g := xq) (h := xq)
    (IsConj.refl xq)
  have hBQ : (∑ μ ∈ CharCore.Irr (G ⧸ H), Complex.normSq (μ xq)) =
      ((Nat.card (Subgroup.centralizer ({xq} : Set (G ⧸ H))) : ℕ) : ℝ) := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_natCast, ← hcolQ]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Complex.mul_conj]
  -- ## The map `C_G(x) → C_{G/H}(x̄)` is injective
  let f : Subgroup.centralizer ({x} : Set G) → Subgroup.centralizer ({xq} : Set (G ⧸ H)) :=
    fun g => ⟨QuotientGroup.mk (g : G), by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have hg : x * (g : G) = (g : G) * x :=
        (Subgroup.mem_centralizer_iff.mp g.2) x (Set.mem_singleton x)
      rw [hxq, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hg]⟩
  have hf_inj : Function.Injective f := by
    intro g1 g2 h
    have hval : QuotientGroup.mk (s := H) (g1 : G) =
        QuotientGroup.mk (s := H) (g2 : G) := by
      simpa [f] using congrArg Subtype.val h
    have hmem : (g1 : G)⁻¹ * (g2 : G) ∈ H := QuotientGroup.eq.mp hval
    have hcent : (g1 : G)⁻¹ * (g2 : G) ∈ Subgroup.centralizer ({x} : Set G) := by
      simpa using (g1⁻¹ * g2).2
    have hbot : (g1 : G)⁻¹ * (g2 : G) ∈ (⊥ : Subgroup G) := by
      rw [← hx]
      exact ⟨hcent, hmem⟩
    have h1 : (g1 : G)⁻¹ * (g2 : G) = 1 := by simpa using hbot
    exact Subtype.ext (inv_mul_eq_one.mp h1)
  have hcard_le : Nat.card (Subgroup.centralizer ({x} : Set G)) ≤
      Nat.card (Subgroup.centralizer ({xq} : Set (G ⧸ H))) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective f hf_inj
  have hcard_leR : ((Nat.card (Subgroup.centralizer ({x} : Set G)) : ℕ) : ℝ) ≤
      ((Nat.card (Subgroup.centralizer ({xq} : Set (G ⧸ H))) : ℕ) : ℝ) :=
    Nat.cast_le.mpr hcard_le
  -- ## Inflation of irreducible characters of `G ⧸ H`
  have hInflIrr : ∀ μ ∈ CharCore.Irr (G ⧸ H),
      Work.Clifford.inflateFun H μ ∈ CharCore.Irr G := by
    intro μ hμ
    have hβ : μ ∈ Work.Clifford.Irr (G ⧸ H) := (Work.Clifford.mem_Irr_charCore_iff').mpr hμ
    have hθ : Work.Clifford.principalChar H ∈ Work.Clifford.Irr H :=
      (Work.Clifford.mem_Irr_charCore_iff').mpr (CharCore.principalChar_mem_Irr (G := H))
    have hχ : Work.Clifford.principalChar G ∈ Work.Clifford.Irr G :=
      (Work.Clifford.mem_Irr_charCore_iff').mpr (CharCore.principalChar_mem_Irr (G := G))
    have hext : Work.Clifford.Extends H (Work.Clifford.principalChar G)
        (Work.Clifford.principalChar H) := rfl
    have h := Work.Clifford.gallagher_mul_inflate_irr (N := H) hθ hχ hext hβ
    have hpc : Work.Clifford.principalChar G * Work.Clifford.inflateFun H μ =
        Work.Clifford.inflateFun H μ := by
      ext g; simp [Work.Clifford.principalChar]
    rw [hpc] at h
    exact (Work.Clifford.mem_Irr_charCore_iff').mp h
  -- Inflation is trivial on `H`, so `H` is contained in the kernel.
  have hInflKer : ∀ μ : G ⧸ H → ℂ,
      (H : Set G) ≤ CharCore.charKernel (Work.Clifford.inflateFun H μ) := by
    intro μ n hn
    have hn1 : QuotientGroup.mk (n : G) = (1 : G ⧸ H) := (QuotientGroup.eq_one_iff (n : G)).mpr hn
    have h11 : QuotientGroup.mk (1 : G) = (1 : G ⧸ H) := QuotientGroup.mk_one H
    show μ (QuotientGroup.mk (n : G)) = μ (QuotientGroup.mk (1 : G))
    rw [hn1, h11]
  -- Inflation is injective.
  have hInflInj : Set.InjOn (fun μ : G ⧸ H → ℂ => Work.Clifford.inflateFun H μ)
      ((CharCore.Irr (G ⧸ H) : Finset (G ⧸ H → ℂ)) : Set (G ⧸ H → ℂ)) := by
    intro μ _ μ' _ h
    funext k
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective k
    have := congrFun h g
    simpa [Work.Clifford.inflateFun_apply] using this
  -- ## The sum over the `λ ∈ Irr G` with `H` in the kernel
  set Fset : Finset (G → ℂ) :=
    (CharCore.Irr G).filter (fun χ => (H : Set G) ≤ CharCore.charKernel χ) with hFset
  have himg_eq : (∑ χ ∈ (CharCore.Irr (G ⧸ H)).image (fun μ => Work.Clifford.inflateFun H μ),
        Complex.normSq (χ x)) = ∑ μ ∈ CharCore.Irr (G ⧸ H), Complex.normSq (μ xq) := by
    rw [Finset.sum_image hInflInj]
    refine Finset.sum_congr rfl fun μ _ => ?_
    show Complex.normSq (μ (QuotientGroup.mk x)) = Complex.normSq (μ xq)
    rw [hxq]
  have himg_le : (∑ μ ∈ CharCore.Irr (G ⧸ H), Complex.normSq (μ xq)) ≤
      ∑ χ ∈ Fset, Complex.normSq (χ x) := by
    rw [← himg_eq]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro χ hχ
      obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hχ
      rw [hFset, Finset.mem_filter]
      exact ⟨hInflIrr μ hμ, hInflKer μ⟩
    · intro χ _ _
      exact Complex.normSq_nonneg _
  have hFset_le : (∑ χ ∈ Fset, Complex.normSq (χ x)) ≤
      (∑ χ ∈ CharCore.Irr G, Complex.normSq (χ x)) := by
    rw [hFset]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro χ _ _
    exact Complex.normSq_nonneg _
  -- ## Both sums equal `|C_G(x)|`
  have hFEq : (∑ χ ∈ Fset, Complex.normSq (χ x)) =
      (∑ χ ∈ CharCore.Irr G, Complex.normSq (χ x)) := by
    apply le_antisymm hFset_le
    rw [hAG]
    calc ((Nat.card (Subgroup.centralizer ({x} : Set G)) : ℕ) : ℝ)
        ≤ ((Nat.card (Subgroup.centralizer ({xq} : Set (G ⧸ H))) : ℕ) : ℝ) := hcard_leR
      _ = ∑ μ ∈ CharCore.Irr (G ⧸ H), Complex.normSq (μ xq) := hBQ.symm
      _ ≤ ∑ χ ∈ Fset, Complex.normSq (χ x) := himg_le
  -- ## The characters outside the kernel contribute nothing
  have hcompl : (∑ χ ∈ (CharCore.Irr G).filter (fun χ => ¬ (H : Set G) ≤ CharCore.charKernel χ),
        Complex.normSq (χ x)) = 0 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (CharCore.Irr G)
      (fun χ => (H : Set G) ≤ CharCore.charKernel χ) (fun χ => Complex.normSq (χ x))
    rw [hFset] at hFEq
    rw [hFEq] at hsplit
    linarith [hsplit]
  -- ## Conclusion
  have hlam_not : ¬ ((H : Set G) ≤ CharCore.charKernel lam) := by
    intro hle
    obtain ⟨h, hh, hne⟩ := hk
    exact hne (hle hh)
  have hlam_mem : lam ∈ (CharCore.Irr G).filter
      (fun χ => ¬ (H : Set G) ≤ CharCore.charKernel χ) :=
    Finset.mem_filter.mpr ⟨hlam, hlam_not⟩
  have hzero : Complex.normSq (lam x) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun χ _ => Complex.normSq_nonneg (χ x))).mp hcompl
      lam hlam_mem
  exact Complex.normSq_eq_zero.mp hzero

end Work.Tame
