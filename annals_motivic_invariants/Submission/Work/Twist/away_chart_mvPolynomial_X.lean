import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.Twist.away_chart_mvPolynomial
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist
open MvPolynomial HomogeneousLocalization

noncomputable section

/-! ## The dehomogenisation at an arbitrary chart variable

`away_chart_mvPolynomial` proves that the degree-zero part `A⁰_{X₀}` of the localisation of
`𝕜[X₀,…,Xₙ]` at `X₀` is a polynomial ring, via the dehomogenisation `chartDhom` (set `X₀ = 1`).

Here we get the analogous statement for the chart at `X_i`, for an arbitrary index `i`, by
conjugating with the coordinate transposition `X₀ ↔ X_i`: the map `chartDhomX` below is
`chartDhom ∘ (rename along the transposition)`, i.e. the dehomogenisation setting `X_i = 1`.
Everything else is then a verbatim copy of the `X₀` argument. -/

/-- The transposition of the coordinates `0` and `i` of `Fin (n + 1)`. -/
def chartSwap {n : ℕ} (i : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap (0 : Fin (n + 1)) i

@[simp]
lemma chartSwap_zero {n : ℕ} (i : Fin (n + 1)) : chartSwap i 0 = i :=
  Equiv.swap_apply_left _ _

@[simp]
lemma chartSwap_self {n : ℕ} (i : Fin (n + 1)) : chartSwap i i = 0 :=
  Equiv.swap_apply_right _ _

@[simp]
lemma chartSwap_involutive {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 1)) :
    chartSwap i (chartSwap i j) = j :=
  Equiv.swap_apply_self _ _ _

/-- **Dehomogenisation at `X_i`.**  The ring homomorphism `𝕜[X₀,…,Xₙ] →+* 𝕜[X₁,…,Xₙ]`
substituting `X_i = 1` and reindexing the remaining variables: it is `chartDhom` conjugated by the
coordinate transposition `X₀ ↔ X_i`. -/
def chartDhomX (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) 𝕜 →+* MvPolynomial (Fin n) 𝕜 :=
  (chartDhom 𝕜 n).comp (MvPolynomial.rename (chartSwap i)).toRingHom

lemma chartDhomX_apply (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (i : Fin (n + 1))
    (x : MvPolynomial (Fin (n + 1)) 𝕜) :
    chartDhomX 𝕜 n i x = chartDhom 𝕜 n (MvPolynomial.rename (chartSwap i) x) := rfl

/-- `chartDhomX` sends the localised variable `X_i` to `1`. -/
lemma chartDhomX_X_self (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    chartDhomX 𝕜 n i (MvPolynomial.X i) = 1 := by
  rw [chartDhomX_apply, MvPolynomial.rename_X, chartSwap_self]
  exact chartDhom_X_zero 𝕜 n

/-- `chartDhomX X_i * 1 = 1`, the form in which `X_i` is fed to `Localization.awayLift`. -/
lemma chartDhomX_mul_one (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    chartDhomX 𝕜 n i (MvPolynomial.X i) * 1 = 1 := by
  rw [mul_one, chartDhomX_X_self]

/-- `chartDhomX X_i = 1` is a unit, so `chartDhomX` inverts `X_i`. -/
lemma chartDhomXUnit (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    IsUnit (chartDhomX 𝕜 n i (MvPolynomial.X i)) :=
  isUnit_iff_exists_inv.mpr ⟨1, chartDhomX_mul_one 𝕜 n i⟩

/-- The variable `X_i` is homogeneous of degree one. -/
lemma Xi_mem_stdGrading (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial.X i ∈ stdGrading 𝕜 n 1 :=
  MvPolynomial.isHomogeneous_X _ i

/-- **The chart isomorphism at `X_i`, as a map.**  `chartDhomX` inverts `X_i`, so it descends to
the localisation `Localization.Away X_i`; restricting to the degree-zero part gives
`A⁰_{X_i} →+* 𝕜[X₁,…,Xₙ]`. -/
def chartPsiX (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    Away (stdGrading 𝕜 n) (MvPolynomial.X i) →+* MvPolynomial (Fin n) 𝕜 :=
  (Localization.awayLift (chartDhomX 𝕜 n i) (MvPolynomial.X i)
      (chartDhomXUnit 𝕜 n i)).comp
    (algebraMap (Away (stdGrading 𝕜 n) (MvPolynomial.X i))
      (Localization.Away (MvPolynomial.X i)))

/-- **`chartPsiX` on a fraction.**  Every element of `A⁰_{X_i}` is `a / X_i ^ N` with `a`
homogeneous of degree `N` (`Away.mk`), and `chartPsiX` sends it to `chartDhomX a`. -/
lemma chartPsiX_awayMk (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (i : Fin (n + 1)) (N : ℕ)
    (a : MvPolynomial (Fin (n + 1)) 𝕜) (ha : a ∈ stdGrading 𝕜 n (N • 1)) :
    chartPsiX 𝕜 n i (Away.mk (stdGrading 𝕜 n) (Xi_mem_stdGrading 𝕜 n i) N a ha)
      = chartDhomX 𝕜 n i a := by
  rw [chartPsiX, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  simpa using (Localization.awayLift_mk (chartDhomX 𝕜 n i) (MvPolynomial.X i) a 1
    (chartDhomX_mul_one 𝕜 n i) N)

/-- A homogeneous polynomial of degree `N` which is killed by the dehomogenisation `X_i = 1` is
zero: conjugate with the transposition and apply `chartDhom_eq_zero`. -/
lemma chartDhomX_eq_zero (𝕜 : Type) [Field 𝕜] (n : ℕ) (i : Fin (n + 1)) {N : ℕ}
    {x : MvPolynomial (Fin (n + 1)) 𝕜} (hx : x.IsHomogeneous N)
    (h : chartDhomX 𝕜 n i x = 0) : x = 0 := by
  have hx' : (MvPolynomial.rename (chartSwap i) x).IsHomogeneous N := hx.rename_isHomogeneous
  have h0 : chartDhom 𝕜 n (MvPolynomial.rename (chartSwap i) x) = 0 := h
  have hy : MvPolynomial.rename (chartSwap i) x = 0 := chartDhom_eq_zero' 𝕜 n hx' h0
  exact MvPolynomial.rename_injective (chartSwap i) (chartSwap i).injective
    (by rw [hy, map_zero])

/-! ## `chartPsiX` is bijective -/

/-- The reindexing `𝕜[X₁,…,Xₙ] → 𝕜[X₀,…,Xₙ]` which is a section of `chartDhomX`: it sends `X_j`
to `X_{σ (j+1)}`, where `σ` is the transposition. -/
lemma chartDhomX_rename_sec (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (i : Fin (n + 1))
    (p : MvPolynomial (Fin n) 𝕜) :
    chartDhomX 𝕜 n i (MvPolynomial.rename ((chartSwap i) ∘ Fin.succ) p) = p := by
  have h : (chartDhomX 𝕜 n i).comp
      (MvPolynomial.rename ((chartSwap i) ∘ Fin.succ)).toRingHom
      = RingHom.id (MvPolynomial (Fin n) 𝕜) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [chartDhomX, chartDhom]
    · intro j
      rw [RingHom.comp_apply, RingHom.id_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        MvPolynomial.rename_X, Function.comp_apply, chartDhomX_apply, MvPolynomial.rename_X]
      rw [show chartSwap i (chartSwap i (Fin.succ j)) = Fin.succ j from chartSwap_involutive i _]
      exact chartDhom_X_succ 𝕜 n j
  exact RingHom.congr_fun h p

/-- **Surjectivity.**  For `p : 𝕜[X₁,…,Xₙ]` we take the sum over the homogeneous components of
`p` of the elements `ren (p_k) / X_i ^ k`, where `ren` is the reindexing
`X_j ↦ X_{σ (j+1)}`: `chartDhomX (ren q) = q`. -/
lemma chartPsiX_surjective (𝕜 : Type) [Field 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    Function.Surjective (chartPsiX 𝕜 n i) := by
  intro p
  refine ⟨∑ k ∈ Finset.range (p.totalDegree + 1),
      Away.mk (stdGrading 𝕜 n) (Xi_mem_stdGrading 𝕜 n i) k
        (MvPolynomial.rename ((chartSwap i) ∘ Fin.succ)
          (MvPolynomial.homogeneousComponent k p))
        (by simpa using (MvPolynomial.homogeneousComponent_mem k p).rename_isHomogeneous), ?_⟩
  rw [map_sum]
  simp only [chartPsiX_awayMk, chartDhomX_rename_sec]
  exact MvPolynomial.sum_homogeneousComponent p

/-- In the localisation of `𝕜[X₀,…,Xₙ]` at `X_i`, multiplying numerator and denominator of a
fraction by `X_i ^ k` does not change it. -/
lemma localization_mk_mul_pow_X (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (i : Fin (n + 1))
    (a : MvPolynomial (Fin (n + 1)) 𝕜)
    (s : Submonoid.powers (MvPolynomial.X i)) (k : ℕ) :
    Localization.mk a s = Localization.mk (a * MvPolynomial.X i ^ k)
      (s * ⟨MvPolynomial.X i ^ k, by use k⟩) := by
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, one_mul, Submonoid.coe_mul]
  first | refl_ring1 | ring

/-- **Injectivity.**  If `chartPsiX (a / X_i ^ N) = chartPsiX (b / X_i ^ M)` then
`chartDhomX a = chartDhomX b`.  Assuming `N ≤ M`, the element `a * X_i ^ (M - N) - b` is
homogeneous of degree `M` and is killed by `chartDhomX`, hence is zero by `chartDhomX_eq_zero`;
so `b = a * X_i ^ (M - N)` and the two fractions agree after rescaling the numerator and
denominator of `a / X_i ^ N` by `X_i ^ (M - N)`. -/
lemma chartPsiX_injective (𝕜 : Type) [Field 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    Function.Injective (chartPsiX 𝕜 n i) := by
  intro z w hzw
  obtain ⟨N, a, ha, rfl⟩ := Away.mk_surjective (stdGrading 𝕜 n) (Xi_mem_stdGrading 𝕜 n i) z
  obtain ⟨M, b, hb, rfl⟩ := Away.mk_surjective (stdGrading 𝕜 n) (Xi_mem_stdGrading 𝕜 n i) w
  rw [chartPsiX_awayMk 𝕜 n i N a ha, chartPsiX_awayMk 𝕜 n i M b hb] at hzw
  have key : ∀ {N M : ℕ} (hNM : N ≤ M) (a b : MvPolynomial (Fin (n + 1)) 𝕜)
      (ha : a ∈ stdGrading 𝕜 n (N • 1)) (hb : b ∈ stdGrading 𝕜 n (M • 1)),
      chartDhomX 𝕜 n i a = chartDhomX 𝕜 n i b →
      Away.mk (stdGrading 𝕜 n) (Xi_mem_stdGrading 𝕜 n i) N a ha
        = Away.mk (stdGrading 𝕜 n) (Xi_mem_stdGrading 𝕜 n i) M b hb := by
    intro N M hNM a b ha hb h
    have ha' : a.IsHomogeneous N := by simpa using ha
    have hb' : b.IsHomogeneous M := by simpa using hb
    have hc' : (a * MvPolynomial.X i ^ (M - N)).IsHomogeneous M := by
      have h1 : (MvPolynomial.X i ^ (M - N) :
          MvPolynomial (Fin (n + 1)) 𝕜).IsHomogeneous (M - N) :=
        MvPolynomial.isHomogeneous_X_pow _ _
      have h2 := ha'.mul h1
      rwa [Nat.add_sub_cancel' hNM] at h2
    have hkey : a * MvPolynomial.X i ^ (M - N) - b = 0 := by
      apply chartDhomX_eq_zero 𝕜 n i (hc'.sub hb')
      rw [map_sub, map_mul, map_pow, chartDhomX_X_self, one_pow, mul_one, h, sub_self]
    have hcb : a * MvPolynomial.X i ^ (M - N) = b := sub_eq_zero.mp hkey
    apply HomogeneousLocalization.val_injective
    rw [Away.val_mk, Away.val_mk, ← hcb, localization_mk_mul_pow_X 𝕜 n i a _ (M - N)]
    congr 1
    exact Subtype.ext (by simp [← pow_add, Nat.add_sub_cancel' hNM])
  rcases le_total N M with hNM | hMN
  · exact key hNM a b ha hb hzw
  · exact (key hMN b a hb ha hzw.symm).symm

/-- **Every chart ring of `ℙⁿ` in the standard grading is a polynomial ring.**  The degree-zero part
of the homogeneous localization of `𝕜[X₀,…,Xₙ]` at `X_i` — the ring of the affine chart
`D₊(X_i) ≅ Spec (A⁰_{X_i})` of `ℙⁿ = Proj 𝕜[X₀,…,Xₙ]` — is isomorphic to `𝕜[y₁,…,yₙ]`, for every
chart index `i`.

This extends `Work.Twist.away_chart_mvPolynomial`
(`Submission/Work/Twist/away_chart_mvPolynomial.lean`, the case `i = 0`, proved via the
dehomogenisation `Work.Twist.chartDhom` and the map `Work.Twist.chartPsi`).  It is what the cover
argument for `ProjectiveModelGap 𝕜 n` needs: `Proj.iSup_basicOpen_eq_top` covers `ℙⁿ` by all the
charts `D₊(X_i)`, so smoothness and the dimension statement must be verified on each of them.

Route for general `i`: the automorphism of `𝕜[X₀,…,Xₙ]` induced by the transposition `X_0 ↔ X_i` is
homogeneous of degree `1` on generators, so it induces `A⁰_{X_0} ≅ A⁰_{X_i`
(`HomogeneousLocalization.Away.map`, with `Away.map_comp`/`Away.map_id`), which composes with the
`X_0` chart isomorphism.  The case `n = 0` degenerates to `𝕜 ≅ MvPolynomial (Fin 0) 𝕜`. -/
theorem away_chart_mvPolynomial_X (𝕜 : Type) [Field 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    Nonempty (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
      (MvPolynomial.X i) ≃+* MvPolynomial (Fin n) 𝕜) :=
  ⟨RingEquiv.ofBijective (chartPsiX 𝕜 n i)
    ⟨chartPsiX_injective 𝕜 n i, chartPsiX_surjective 𝕜 n i⟩⟩

end

end Work.Twist
