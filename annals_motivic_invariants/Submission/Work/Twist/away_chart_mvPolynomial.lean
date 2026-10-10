import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.Twist.chartDhom_eq_zero
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

/-! ## The standard grading of `𝕜[X₀,…,Xₙ]` and the chart ring `A⁰_{X₀}`

We fix the notation used below.  `stdGrading 𝕜 n` is the standard grading of `𝕜[X₀,…,Xₙ]` (every
variable has degree one), i.e. Mathlib's `MvPolynomial.homogeneousSubmodule`, and `ChartAway 𝕜 n`
is the degree-zero part `A⁰_{X₀}` of the localisation at `X₀`, the coordinate ring of the affine
chart `D₊(X₀)` of `ℙⁿ`. -/

/-- The standard grading of `𝕜[X₀,…,Xₙ]`: every variable has degree one. -/
abbrev stdGrading (𝕜 : Type) [CommRing 𝕜] (n : ℕ) :
    ℕ → Submodule 𝕜 (MvPolynomial (Fin (n + 1)) 𝕜) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜

/-- The coordinate ring `A⁰_{X₀}` of the affine chart `D₊(X₀)` of `ℙⁿ`. -/
abbrev ChartAway (𝕜 : Type) [CommRing 𝕜] (n : ℕ) : Type :=
  HomogeneousLocalization.Away (stdGrading 𝕜 n) (MvPolynomial.X (0 : Fin (n + 1)))

/-- The variable `X₀` is homogeneous of degree one. -/
lemma X0_mem_stdGrading (𝕜 : Type) [CommRing 𝕜] (n : ℕ) :
    MvPolynomial.X (0 : Fin (n + 1)) ∈ stdGrading 𝕜 n 1 :=
  MvPolynomial.isHomogeneous_X _ _

/-! ## The dehomogenisation `X₀ ↦ 1` -/

/-- **Dehomogenisation.**  The ring homomorphism `𝕜[X₀,…,Xₙ] →+* 𝕜[X₁,…,Xₙ]` substituting
`X₀ = 1`, `X_{i+1} = X_i`. -/
def chartDhom (𝕜 : Type) [CommRing 𝕜] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) 𝕜 →+* MvPolynomial (Fin n) 𝕜 :=
  MvPolynomial.eval₂Hom (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜))
    (Fin.cases 1 (fun j => MvPolynomial.X j))

/-- `chartDhom` sends the localised variable `X₀` to `1`. -/
lemma chartDhom_X_zero (𝕜 : Type) [CommRing 𝕜] (n : ℕ) :
    chartDhom 𝕜 n (MvPolynomial.X (0 : Fin (n + 1))) = 1 := by
  simp [chartDhom]

/-- `chartDhom` sends `X_{i+1}` to `X_i`. -/
lemma chartDhom_X_succ (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (j : Fin n) :
    chartDhom 𝕜 n (MvPolynomial.X (j.succ : Fin (n + 1))) = MvPolynomial.X j := by
  simp [chartDhom]

/-- The reindexing `𝕜[X₁,…,Xₙ] → 𝕜[X₀,…,Xₙ]`, `X_j ↦ X_{j+1}`, is a section of `chartDhom`. -/
lemma chartDhom_rename_succ (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (p : MvPolynomial (Fin n) 𝕜) :
    chartDhom 𝕜 n (MvPolynomial.rename (Fin.succ : Fin n → Fin (n + 1)) p) = p := by
  have h : (chartDhom 𝕜 n).comp
      (MvPolynomial.rename (Fin.succ : Fin n → Fin (n + 1)) :
        MvPolynomial (Fin n) 𝕜 →ₐ[𝕜] MvPolynomial (Fin (n + 1)) 𝕜).toRingHom
      = RingHom.id (MvPolynomial (Fin n) 𝕜) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [chartDhom]
    · intro i; simp [chartDhom_X_succ]
  exact RingHom.congr_fun h p

/-- `chartDhom X₀ * 1 = 1`, the form in which `X₀` is fed to `Localization.awayLift`. -/
lemma chartDhom_mul_one (𝕜 : Type) [CommRing 𝕜] (n : ℕ) :
    chartDhom 𝕜 n (MvPolynomial.X (0 : Fin (n + 1))) * 1 = 1 := by
  rw [mul_one, chartDhom_X_zero]

/-- `chartDhom X₀ = 1` is a unit, so `chartDhom` inverts `X₀`. -/
lemma chartDhomUnit (𝕜 : Type) [CommRing 𝕜] (n : ℕ) :
    IsUnit (chartDhom 𝕜 n (MvPolynomial.X (0 : Fin (n + 1)))) :=
  isUnit_iff_exists_inv.mpr ⟨1, chartDhom_mul_one 𝕜 n⟩

/-- **The chart isomorphism, as a map.**  `chartDhom` inverts `X₀`, so it descends to the
localisation `Localization.Away X₀`; restricting to the degree-zero part gives
`A⁰_{X₀} →+* 𝕜[X₁,…,Xₙ]`, `X_j / X₀ ↦ X_j`. -/
def chartPsi (𝕜 : Type) [CommRing 𝕜] (n : ℕ) : ChartAway 𝕜 n →+* MvPolynomial (Fin n) 𝕜 :=
  (Localization.awayLift (chartDhom 𝕜 n) (MvPolynomial.X (0 : Fin (n + 1)))
      (chartDhomUnit 𝕜 n)).comp
    (algebraMap (ChartAway 𝕜 n) (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)))))

/-- **`chartPsi` on a fraction.**  Every element of `A⁰_{X₀}` is `a / X₀ ^ N` with `a` homogeneous
of degree `N` (`Away.mk`), and `chartPsi` sends it to `chartDhom a`. -/
lemma chartPsi_awayMk (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (N : ℕ)
    (a : MvPolynomial (Fin (n + 1)) 𝕜) (ha : a ∈ stdGrading 𝕜 n (N • 1)) :
    chartPsi 𝕜 n (Away.mk (stdGrading 𝕜 n) (X0_mem_stdGrading 𝕜 n) N a ha)
      = chartDhom 𝕜 n a := by
  rw [chartPsi, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  simpa using (Localization.awayLift_mk (chartDhom 𝕜 n) (MvPolynomial.X (0 : Fin (n + 1))) a 1
    (chartDhom_mul_one 𝕜 n) N)

/-- The version of `Work.Twist.chartDhom_eq_zero` phrased with `chartDhom` (of which
`MvPolynomial.eval₂Hom` there is the definitional unfolding), for rewriting convenience. -/
lemma chartDhom_eq_zero' (𝕜 : Type) [Field 𝕜] (n : ℕ) {N : ℕ}
    {x : MvPolynomial (Fin (n + 1)) 𝕜} (hx : x.IsHomogeneous N) (h : chartDhom 𝕜 n x = 0) :
    x = 0 := by
  apply chartDhom_eq_zero 𝕜 n hx
  exact h

/-! ## `chartPsi` is bijective -/

/-- **Surjectivity.**  `chartPsi` maps the fraction `Away.mk k (X_{j+1}…)` to the monomial, so the
image contains all monomials; additivity finishes.  Concretely, for `p : 𝕜[X₁,…,Xₙ]` we take the
sum over the homogeneous components of `p` of the elements
`ren (p_k) / X₀ ^ k`, where `ren` is the reindexing `X_j ↦ X_{j+1}`: `chartDhom (ren q) = q`. -/
lemma chartPsi_surjective (𝕜 : Type) [Field 𝕜] (n : ℕ) : Function.Surjective (chartPsi 𝕜 n) := by
  intro p
  refine ⟨∑ k ∈ Finset.range (p.totalDegree + 1),
      Away.mk (stdGrading 𝕜 n) (X0_mem_stdGrading 𝕜 n) k
        (MvPolynomial.rename (Fin.succ : Fin n → Fin (n + 1))
          (MvPolynomial.homogeneousComponent k p))
        (by simpa using (MvPolynomial.homogeneousComponent_mem k p).rename_isHomogeneous), ?_⟩
  rw [map_sum]
  simp only [chartPsi_awayMk, chartDhom_rename_succ]
  exact MvPolynomial.sum_homogeneousComponent p

/-- In the localisation of `𝕜[X₀,…,Xₙ]` at `X₀`, multiplying numerator and denominator of a
fraction by `X₀ ^ k` does not change it. -/
lemma localization_mk_mul_pow (𝕜 : Type) [CommRing 𝕜] (n : ℕ)
    (a : MvPolynomial (Fin (n + 1)) 𝕜)
    (s : Submonoid.powers (MvPolynomial.X (0 : Fin (n + 1)))) (k : ℕ) :
    Localization.mk a s = Localization.mk (a * MvPolynomial.X (0 : Fin (n + 1)) ^ k)
      (s * ⟨MvPolynomial.X (0 : Fin (n + 1)) ^ k, by use k⟩) := by
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, one_mul, Submonoid.coe_mul]
  first | refl_ring1 | ring

/-- **Injectivity.**  If `chartPsi (a / X₀ ^ N) = chartPsi (b / X₀ ^ M)` then
`chartDhom a = chartDhom b`.  Assuming `N ≤ M`, the element `a * X₀ ^ (M - N) - b` is homogeneous
of degree `M` and is killed by `chartDhom`, hence is zero by
`Work.Twist.chartDhom_eq_zero`; so `b = a * X₀ ^ (M - N)` and the two fractions agree after
rescaling the numerator and denominator of `a / X₀ ^ N` by `X₀ ^ (M - N)`. -/
lemma chartPsi_injective (𝕜 : Type) [Field 𝕜] (n : ℕ) : Function.Injective (chartPsi 𝕜 n) := by
  intro z w hzw
  obtain ⟨N, a, ha, rfl⟩ := Away.mk_surjective (stdGrading 𝕜 n) (X0_mem_stdGrading 𝕜 n) z
  obtain ⟨M, b, hb, rfl⟩ := Away.mk_surjective (stdGrading 𝕜 n) (X0_mem_stdGrading 𝕜 n) w
  rw [chartPsi_awayMk 𝕜 n N a ha, chartPsi_awayMk 𝕜 n M b hb] at hzw
  have key : ∀ {N M : ℕ} (hNM : N ≤ M) (a b : MvPolynomial (Fin (n + 1)) 𝕜)
      (ha : a ∈ stdGrading 𝕜 n (N • 1)) (hb : b ∈ stdGrading 𝕜 n (M • 1)),
      chartDhom 𝕜 n a = chartDhom 𝕜 n b →
      Away.mk (stdGrading 𝕜 n) (X0_mem_stdGrading 𝕜 n) N a ha
        = Away.mk (stdGrading 𝕜 n) (X0_mem_stdGrading 𝕜 n) M b hb := by
    intro N M hNM a b ha hb h
    have ha' : a.IsHomogeneous N := by simpa using ha
    have hb' : b.IsHomogeneous M := by simpa using hb
    have hc' : (a * MvPolynomial.X (0 : Fin (n + 1)) ^ (M - N)).IsHomogeneous M := by
      have h1 : (MvPolynomial.X (0 : Fin (n + 1)) ^ (M - N) :
          MvPolynomial (Fin (n + 1)) 𝕜).IsHomogeneous (M - N) :=
        MvPolynomial.isHomogeneous_X_pow _ _
      have h2 := ha'.mul h1
      rwa [Nat.add_sub_cancel' hNM] at h2
    have hkey : a * MvPolynomial.X (0 : Fin (n + 1)) ^ (M - N) - b = 0 := by
      apply chartDhom_eq_zero' 𝕜 n (hc'.sub hb')
      rw [map_sub, map_mul, map_pow, chartDhom_X_zero, one_pow, mul_one, h, sub_self]
    have hcb : a * MvPolynomial.X (0 : Fin (n + 1)) ^ (M - N) = b := sub_eq_zero.mp hkey
    apply HomogeneousLocalization.val_injective
    rw [Away.val_mk, Away.val_mk, ← hcb, localization_mk_mul_pow 𝕜 n a _ (M - N)]
    congr 1
    exact Subtype.ext (by simp [← pow_add, Nat.add_sub_cancel' hNM])
  rcases le_total N M with hNM | hMN
  · exact key hNM a b ha hb hzw
  · exact (key hMN b a hb ha hzw.symm).symm

/-- **The chart ring of `ℙⁿ` in the standard grading is a polynomial ring.**  The degree-zero part
of the homogeneous localization of `𝕜[X₀,…,Xₙ]` at `X₀` — the ring of the affine chart
`D₊(X₀) ≅ Spec (A⁰_{X₀})` of `ℙⁿ = Proj 𝕜[X₀,…,Xₙ]` — is isomorphic to `𝕜[y₁,…,yₙ]`, the
isomorphism being `y_j ↦ X_j / X₀`.

This is the missing algebra input of `ProjectiveModelGap` (`Work.PointlessIndexFive.Model`, the
`Smooth`/`GeometricallyIntegral`/`topologicalKrullDim` of the projective model): with it, smoothness
and dimension of the projective charts reduce to the corresponding facts for the polynomial ring
(`AlgebraicGeometry.AffineSpace`, `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`).

Surjectivity is the content of Mathlib's `Away.adjoin_mk_prod_pow_eq_top` (the `Away` ring is
generated over `𝒜 0` by monomials divided by powers of `X₀`, which are the monomials in the
`X_j/X₀`).  For injectivity, note that `Localization.Away X₀` admits a ring endomorphism with
`X₀ ↦ 1`, `X_j ↦ X_j / X₀`; it restricts to a section of the canonical inclusion of the degree-zero
part, which forces injectivity.  Elements of `Away 𝒜 X₀` are represented by `num / den` with `num`,
`den = X₀^n` homogeneous of the same degree (`HomogeneousLocalization.NumDenSameDeg`), and the
statement is invariant under `Nonempty`. -/
theorem away_chart_mvPolynomial (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    Nonempty (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
      (MvPolynomial.X 0) ≃+* MvPolynomial (Fin n) 𝕜) :=
  ⟨RingEquiv.ofBijective (chartPsi 𝕜 n)
    ⟨chartPsi_injective 𝕜 n, chartPsi_surjective 𝕜 n⟩⟩

end

end Work.Twist
