import Mathlib
import Submission.Work.CharCore.classFun_eq_sum_irr
import Submission.Work.Clifford.All
import Submission.Work.Clifford.gallagher_mul_inflate_irr
import Submission.Work.Clifford.FunAPI
import Submission.Work.CharCore.principalChar_mem_Irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame.cfInner_const_coset_eq_zero`

Let `K ⊴ G` be a normal subgroup of a finite group, let `f` be a class function of `G` which is
constant on the left cosets of `K` (`f (n * g) = f g` for `n ∈ K`), and let `θ` be an irreducible
character of `G` which is *not* trivial on `K` (`θ n ≠ θ 1` for some `n ∈ K`).  Then `f` and `θ`
are orthogonal: `⟪f, θ⟫_G = 0`.

Equivalently: the class functions of `G` constant on the cosets of `K` are exactly the inflations
of the class functions of `G ⧸ K`, and none of these has `θ` as a constituent, because the
irreducible constituents of an inflation from `G ⧸ K` are themselves trivial on `K`.

## Proof

1. From `f (n * g) = f g` (`n ∈ K`) and the class function property one gets invariance under
   right multiplication as well: `f (g * n) = f g`.  Hence `f` is constant on the `K`-cosets of
   the *quotient* relation, and descends to a function `ψ` on `G ⧸ K`; `ψ` is again a class
   function, since conjugation in the quotient is conjugation of representatives.
2. `Work.CharCore.classFun_eq_sum_irr` expands `ψ` as `∑_χ ⟪ψ, χ⟫ · χ` over the irreducible
   characters of `G ⧸ K`; inflating gives
   `f = ∑_χ ⟪ψ, χ⟫ • Inf_K χ`.
3. The inflation of an irreducible character of `G ⧸ K` is irreducible in `G`: it is the product
   of the principal character of `G` with the inflation, so Gallagher's theorem
   (`Work.Clifford.gallagher_mul_inflate_irr`) applies.
4. `Inf_K χ ≠ θ`, because `Inf_K χ` is trivial on `K` whereas `θ` is not (this is the hypothesis
   `hk`, via `QuotientGroup.eq_one_iff`).
5. Orthonormality of `Irr G` (`Work.CharCore.irr_orthonormal`) then gives
   `⟪Inf_K χ, θ⟫_G = 0` for every `χ ∈ Irr (G ⧸ K)`, and the sum vanishes by bilinearity.
-/

namespace Work.Tame

theorem cfInner_const_coset_eq_zero {G : Type*} [Group G] [Fintype G] {K : Subgroup G} [K.Normal]
    {θ : G → ℂ} (hθ : θ ∈ Work.CharCore.Irr G) (hk : ∃ n : G, n ∈ K ∧ θ n ≠ θ 1)
    {f : G → ℂ} (hf : Work.CharCore.IsClassFun f)
    (hfinv : ∀ n : G, n ∈ K → ∀ g : G, f (n * g) = f g) :
    Work.Coherence.cfInner f θ = 0 := by
  classical
  -- `f` is invariant under right multiplication by elements of `K` as well.
  have hfinv' : ∀ g n : G, n ∈ K → f (g * n) = f g := by
    intro g n hn
    have h1 : g * n = n * (n⁻¹ * g * n) := by group
    rw [h1, hfinv n hn (n⁻¹ * g * n)]
    simpa using hf g n⁻¹
  -- hence `f` descends to the quotient `G ⧸ K`.
  have hlift : ∀ a b : G, QuotientGroup.leftRel K a b → f a = f b := by
    intro a b hab
    have h : QuotientGroup.mk a = QuotientGroup.mk b := Quotient.sound hab
    have hmem : a⁻¹ * b ∈ K := QuotientGroup.eq.mp h
    calc f a = f (a * (a⁻¹ * b)) := (hfinv' a (a⁻¹ * b) hmem).symm
      _ = f b := by rw [mul_inv_cancel_left]
  let ψ : G ⧸ K → ℂ := Quotient.lift f hlift
  have hψmk : ∀ g : G, ψ (QuotientGroup.mk g) = f g := by
    intro g
    simp [ψ, Quotient.lift_mk]
  -- `ψ` is a class function of the quotient.
  have hψclass : Work.CharCore.IsClassFun ψ := by
    intro g h
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨h', rfl⟩ := QuotientGroup.mk_surjective h
    have h1 : (QuotientGroup.mk h' : G ⧸ K) * (QuotientGroup.mk g' : G ⧸ K) *
        ((QuotientGroup.mk h' : G ⧸ K))⁻¹ = QuotientGroup.mk (h' * g' * h'⁻¹) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h1, hψmk, hψmk]
    exact hf g' h'
  -- expand `ψ` in the irreducible characters of `G ⧸ K` and inflate the expansion.
  have hψsum := Work.CharCore.classFun_eq_sum_irr (G := G ⧸ K) hψclass
  have hf_eq : f = ∑ χ ∈ Work.CharCore.Irr (G ⧸ K), (Work.CharCore.cfInner ψ χ) •
      Work.Clifford.inflateFun K χ := by
    have h1 : Work.Clifford.inflateFun K ψ = f := by
      funext g
      rw [Work.Clifford.inflateFun_apply, hψmk]
    have h2 : Work.Clifford.inflateFun K
        (∑ χ ∈ Work.CharCore.Irr (G ⧸ K), (Work.CharCore.cfInner ψ χ) • χ) =
        ∑ χ ∈ Work.CharCore.Irr (G ⧸ K), (Work.CharCore.cfInner ψ χ) •
          Work.Clifford.inflateFun K χ := by
      funext g
      simp only [Work.Clifford.inflateFun_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← h2, ← hψsum]
    exact h1.symm
  -- the inflation of an irreducible character of `G ⧸ K` is irreducible in `G`.
  have hIrr : ∀ χ ∈ Work.CharCore.Irr (G ⧸ K),
      Work.Clifford.inflateFun K χ ∈ Work.CharCore.Irr G := by
    intro χ hχ
    have hβ : χ ∈ Work.Clifford.Irr (G ⧸ K) := (Work.Clifford.mem_Irr_charCore_iff').mpr hχ
    have hθ0 : Work.Clifford.principalChar K ∈ Work.Clifford.Irr K :=
      (Work.Clifford.mem_Irr_charCore_iff').mpr (Work.CharCore.principalChar_mem_Irr (G := K))
    have hχ0 : Work.Clifford.principalChar G ∈ Work.Clifford.Irr G :=
      (Work.Clifford.mem_Irr_charCore_iff').mpr (Work.CharCore.principalChar_mem_Irr (G := G))
    have hext : Work.Clifford.Extends K (Work.Clifford.principalChar G)
        (Work.Clifford.principalChar K) := rfl
    have h := Work.Clifford.gallagher_mul_inflate_irr (N := K) hθ0 hχ0 hext hβ
    have hpc : Work.Clifford.principalChar G * Work.Clifford.inflateFun K χ =
        Work.Clifford.inflateFun K χ := by
      ext g
      simp [Work.Clifford.principalChar]
    rw [hpc] at h
    exact (Work.Clifford.mem_Irr_charCore_iff').mp h
  -- an inflation from `G ⧸ K` is trivial on `K`, so it is not `θ`.
  have hne : ∀ χ ∈ Work.CharCore.Irr (G ⧸ K), Work.Clifford.inflateFun K χ ≠ θ := by
    intro χ hχ hEq
    obtain ⟨n, hn, hnθ⟩ := hk
    have h1 : Work.Clifford.inflateFun K χ n = Work.Clifford.inflateFun K χ 1 := by
      rw [Work.Clifford.inflateFun_apply, Work.Clifford.inflateFun_apply,
        show QuotientGroup.mk n = (1 : G ⧸ K) from (QuotientGroup.eq_one_iff n).mpr hn,
        QuotientGroup.mk_one]
    rw [hEq] at h1
    exact hnθ h1
  -- the pairing against `θ` kills every term.
  rw [hf_eq]
  change Work.CharCore.cfInner (∑ χ ∈ Work.CharCore.Irr (G ⧸ K), (Work.CharCore.cfInner ψ χ) •
      Work.Clifford.inflateFun K χ) θ = 0
  rw [Work.CharCore.cfInner_sum_smul_left]
  refine Finset.sum_eq_zero (fun χ hχ => ?_)
  have h1 : Work.CharCore.cfInner (Work.Clifford.inflateFun K χ) θ = 0 := by
    rw [Work.CharCore.irr_orthonormal _ _ (hIrr χ hχ) hθ, if_neg (hne χ hχ)]
  rw [h1, mul_zero]

end Work.Tame
