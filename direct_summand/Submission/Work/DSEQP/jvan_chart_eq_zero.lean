import Mathlib
import Submission.Work.DSEQP.gf_defs
import Submission.Work.DSEQP.vanishing_ideal_chart
import Submission.Work.DSEQP.jvan_away_mk_add
import Submission.Work.DSEQP.jvan_dehomog_monomial

/-!
# `Work.DSEQP.jvan_chart_eq_zero`

If `f` lies in the saturation `Jvan i` of the vanishing ideal of `X ⊆ ℙᴺ_A` and `f` is
homogeneous of degree `d`, then the chart section `f / x_j^d` vanishes on `X ∩ D₊(x_j)`.

The mathematical content is that the set of forms with vanishing chart sections is closed
under the operations generating `Jvan i` as an ideal.  Formally one exhibits the
**dehomogenisation** ring hom

`jvanDehomog j : A[x₀,…,x_N] →+* Away 𝒜 (x_j)`,   `f ↦ f(x₀/x_j,…,1,…,x_N/x_j)`

(the map induced by `X_i ↦ X_i/x_j`), shows `jvanDehomog j f = Away.mk hf d f` for `f`
homogeneous of degree `d` (`jvanDehomog_eq_mk`, via the monomial computation
`jvan_dehomog_monomial`), and observes that `⋂_j ker (chartMap i {j} ∘ jvanDehomog j)` is an
ideal containing the generators of `Jvan i`.
-/

open CategoryTheory AlgebraicGeometry
open scoped BigOperators
open HomogeneousLocalization

namespace Work.DSEQP

universe a

section Generic

variable {S : Type*} [CommRing S] {σ : Type*} [SetLike σ S] [AddSubgroupClass σ S]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {f : S} {d : ℕ}

/-- Witness irrelevance for `Away.mk`: the membership proof of the numerator does not matter. -/
lemma jvan_away_mk_irrel (hf : f ∈ 𝒜 d)
    (n : ℕ) (a : S) (ha₁ ha₂ : a ∈ 𝒜 (n • d)) :
    Away.mk 𝒜 hf n a ha₁ = Away.mk 𝒜 hf n a ha₂ := by
  apply HomogeneousLocalization.val_injective
  rfl

/-- Additivity of `Away.mk` with the resulting membership proof left as a variable. -/
lemma jvan_away_mk_add' (hf : f ∈ 𝒜 d) (k : ℕ) (s t : S)
    (hs : s ∈ 𝒜 (k • d)) (ht : t ∈ 𝒜 (k • d)) (hst : s + t ∈ 𝒜 (k • d)) :
    Away.mk 𝒜 hf k s hs + Away.mk 𝒜 hf k t ht = Away.mk 𝒜 hf k (s + t) hst := by
  rw [jvan_away_mk_add hf k s t hs ht]

/-- `Away.mk` of a zero numerator vanishes. -/
lemma jvan_away_mk_zero (hf : f ∈ 𝒜 d) (k : ℕ) (hm : (0 : S) ∈ 𝒜 (k • d)) :
    Away.mk 𝒜 hf k 0 hm = 0 := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_zero]

end Generic

section Main

variable {A : Type a} [CommRing A] {N : ℕ}

/-- **The dehomogenisation at the chart `D₊(x_j)`**, the ring hom `A[x₀,…,x_N] →+* Away 𝒜 (x_j)`
sending `X_i ↦ X_i/x_j`.  It is `MvPolynomial.eval₂Hom` applied to the constants and to the
`X_i ↦ Away.mk hf 1 (X i)`. -/
noncomputable def jvanDehomog (A : Type a) [CommRing A] {N : ℕ} (j : Fin (N + 1)) :
    MvPolynomial (Fin (N + 1)) A →+*
      Away (DSMap.PGr A N) (xS (A := A) ({j} : Finset (Fin (N + 1)))) :=
  MvPolynomial.eval₂Hom
    ((fromZeroRingHom (DSMap.PGr A N)
        (Submonoid.powers (xS (A := A) ({j} : Finset (Fin (N + 1)))))).comp
      (algebraMap A (DSMap.PGr A N 0)))
    (fun i => Away.mk (DSMap.PGr A N) (xS_singleton_mem (A := A) (N := N) j) 1
      (MvPolynomial.X i) (by simpa using DSMap.Mix2.X_mem_PGr i))

/-- `Away.mk` distributes over finite sums of numerators of a fixed degree `d`.  The numerator
and its membership proof are decoupled so that the induction is not blocked by the dependency of
the proof on the sum. -/
lemma jvan_mk_sum_aux (j : Fin (N + 1)) {d : ℕ} {ι : Type*}
    (g : ι → MvPolynomial (Fin (N + 1)) A) (hg : ∀ i, g i ∈ DSMap.PGr A N (d • 1)) :
    ∀ (s : Finset ι) (G : MvPolynomial (Fin (N + 1)) A) (hG : G ∈ DSMap.PGr A N (d • 1)),
      G = (∑ i ∈ s, g i) →
      Away.mk (DSMap.PGr A N) (xS_singleton_mem j) d G hG =
        ∑ i ∈ s, Away.mk (DSMap.PGr A N) (xS_singleton_mem j) d (g i) (hg i) := by
  classical
  intro s
  induction s using Finset.induction with
  | empty =>
    intro G hG hGsum
    rw [Finset.sum_empty] at hGsum
    subst hGsum
    rw [jvan_away_mk_zero]
    simp
  | insert a s ha ih =>
    intro G hG hGsum
    rw [Finset.sum_insert ha] at hGsum
    rw [show Away.mk (DSMap.PGr A N) (xS_singleton_mem j) d G hG =
        Away.mk (DSMap.PGr A N) (xS_singleton_mem j) d (g a + ∑ i ∈ s, g i)
          (hGsum ▸ hG) from away_mk_congr _ rfl hGsum hG (hGsum ▸ hG)]
    rw [← jvan_away_mk_add' (𝒜 := DSMap.PGr A N) (xS_singleton_mem (A := A) (N := N) j) d
        (g a) (∑ i ∈ s, g i) (hg a) (Submodule.sum_mem _ (fun i _ => hg i)) (hGsum ▸ hG)]
    rw [ih (∑ i ∈ s, g i) (Submodule.sum_mem _ (fun i _ => hg i)) rfl]
    rw [Finset.sum_insert ha]

/-- **The dehomogenisation agrees with the chart fraction on homogeneous elements.**  For `f`
homogeneous of degree `d`, `jvanDehomog j f` is `f / x_j^d` in `Away 𝒜 (x_j)`. -/
lemma jvanDehomog_eq_mk (j : Fin (N + 1))
    {f : MvPolynomial (Fin (N + 1)) A} {d : ℕ} (hf : f ∈ Work.DSCOH.homSub A (N + 1) d)
    (hx : f ∈ DSMap.PGr A N (d • 1)) :
    jvanDehomog A j f = Away.mk (DSMap.PGr A N) (xS_singleton_mem j) d f hx := by
  -- every monomial of `f` has degree `d`
  have hdeg : ∀ v ∈ f.support, v.degree = d := by
    intro v hv
    rw [Finsupp.degree_eq_weight_one]
    exact hf (Finsupp.mem_support_iff.mp hv)
  -- the monomials of `f` lie in the degree-`d` piece
  have hmono : ∀ v, MvPolynomial.monomial v (f.coeff v) ∈ DSMap.PGr A N (d • 1) := by
    intro v
    by_cases hv : v ∈ f.support
    · have hd' := hdeg v hv
      simpa [hd'] using (MvPolynomial.mem_homogeneousSubmodule (σ := Fin (N + 1)) (R := A) d
        (MvPolynomial.monomial v (f.coeff v))).mpr
          (MvPolynomial.isHomogeneous_monomial (f.coeff v) hd')
    · have h0 : f.coeff v = 0 := by simpa [Finsupp.mem_support_iff] using hv
      simp [h0]
  have hsumcoeff : f = ∑ v ∈ f.support, MvPolynomial.monomial v (f.coeff v) :=
    (MvPolynomial.support_sum_monomial_coeff f).symm
  -- rewrite the chart fraction as the sum of the chart fractions of the monomials
  have hkey : Away.mk (DSMap.PGr A N) (xS_singleton_mem j) d f hx =
      ∑ v ∈ f.support, Away.mk (DSMap.PGr A N) (xS_singleton_mem j) d
        (MvPolynomial.monomial v (f.coeff v)) (hmono v) := by
    rw [show Away.mk (DSMap.PGr A N) (xS_singleton_mem j) d f hx =
        Away.mk (DSMap.PGr A N) (xS_singleton_mem j) d
          (∑ v ∈ f.support, MvPolynomial.monomial v (f.coeff v))
          (hsumcoeff ▸ hx) from away_mk_congr _ rfl hsumcoeff hx (hsumcoeff ▸ hx)]
    exact jvan_mk_sum_aux (A := A) (N := N) j (fun v => MvPolynomial.monomial v (f.coeff v))
      hmono f.support (∑ v ∈ f.support, MvPolynomial.monomial v (f.coeff v))
      (hsumcoeff ▸ hx) rfl
  rw [hkey, jvanDehomog, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hmono' : MvPolynomial.monomial v (f.coeff v) ∈ DSMap.PGr A N (v.degree • 1) := by
    simpa using (MvPolynomial.mem_homogeneousSubmodule (σ := Fin (N + 1)) (R := A) v.degree
      (MvPolynomial.monomial v (f.coeff v))).mpr
        (MvPolynomial.isHomogeneous_monomial (f.coeff v) rfl)
  rw [show Away.mk (DSMap.PGr A N) (xS_singleton_mem j) d
        (MvPolynomial.monomial v (f.coeff v)) (hmono v) =
      Away.mk (DSMap.PGr A N) (xS_singleton_mem j) v.degree
        (MvPolynomial.monomial v (f.coeff v)) hmono' from
    away_mk_congr _ (hdeg v hv).symm rfl (hmono v) hmono']
  rw [jvan_dehomog_monomial (A := A) (N := N) j v (f.coeff v)]
  rfl

end Main

section Final

variable {A : Type a} [CommRing A] {N : ℕ} {X : AlgebraicGeometry.Scheme.{a}}

theorem jvan_chart_eq_zero (A : Type a) [CommRing A] {N : ℕ} {X : AlgebraicGeometry.Scheme.{a}}
    (i : X ⟶ DSMap.PSpace A N) {f : MvPolynomial (Fin (N + 1)) A} (hf : f ∈ Work.DSEQP.Jvan i)
    (d : ℕ) (hd : f ∈ Work.DSCOH.homSub A (N + 1) d) (j : Fin (N + 1)) :
    Work.DSEQP.chartMap i {j} (Finset.singleton_nonempty j)
      (HomogeneousLocalization.Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_singleton_mem j) d f (by
        simpa [Work.DSEQP.xS_singleton] using hd)) = 0 := by
  -- the intersection of the kernels of the chart maps composed with the dehomogenisation
  have hspan : Jvan i ≤ ⨅ (j : Fin (N + 1)),
      RingHom.ker ((chartMap i {j} (Finset.singleton_nonempty j)).comp (jvanDehomog A j)) := by
    apply Ideal.span_le.mpr
    rintro g ⟨d', hg', hvan⟩
    simp only [SetLike.mem_coe, Ideal.mem_iInf, RingHom.mem_ker]
    intro j
    have hx : g ∈ DSMap.PGr A N (d' • 1) := by simpa using hg'
    change (chartMap i {j} (Finset.singleton_nonempty j)) (jvanDehomog A j g) = 0
    rw [jvanDehomog_eq_mk j hg' hx]
    rw [jvan_away_mk_irrel _ d' g hx (by simpa [xS_singleton] using hg')]
    exact hvan j
  have hK := hspan hf
  simp only [Ideal.mem_iInf, RingHom.mem_ker] at hK
  have hKj := hK j
  have hx : f ∈ DSMap.PGr A N (d • 1) := by simpa using hd
  change (chartMap i {j} (Finset.singleton_nonempty j)) (jvanDehomog A j f) = 0 at hKj
  rw [jvanDehomog_eq_mk j hd hx] at hKj
  rw [jvan_away_mk_irrel _ d f hx (by simpa [xS_singleton] using hd)] at hKj
  exact hKj

end Final

end Work.DSEQP
