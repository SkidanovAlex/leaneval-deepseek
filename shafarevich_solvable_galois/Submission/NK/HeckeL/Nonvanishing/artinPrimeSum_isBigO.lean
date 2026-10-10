import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.FunLike.Fintype
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Submission.NK.HeckeL.Product.prod_artinLSeries_eq_aux
import Submission.NK.HeckeL.Product.tendsto_zetaUnramified_div
import Submission.NK.HeckeL.Series.artinPrimeSum_sub_artinLogEulerProduct_isBigO
import Submission.NK.HeckeL.Series.continuousOn_artinLogEulerProduct
import Submission.NK.HeckeL.Series.exp_artinLogEulerProduct
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain
open scoped BigOperators Classical nonZeroDivisors Topology
open Filter Asymptotics

noncomputable section

namespace NK.HeckeL.Nonvanishing

/-- **A continuous branch of the logarithm of a function tending to a non-zero limit is bounded.**

If `f` is continuous on `(1, ∞)` and `exp ∘ f` tends to a non-zero limit `w` as `s → 1⁺`, then `f`
is `O(1)` near `1⁺`.

Indeed `exp (f s) / w → 1`, so on a small interval `(1, 1+ε)` the auxiliary function
`g s = log (exp (f s) / w) + log w` is a continuous branch of the logarithm of `exp ∘ f`, hence
`f - g` is continuous there with values in the discrete subgroup `2πiℤ`; being defined on a
connected set it is constant, so `f` differs from the bounded function `g` by a constant. -/
lemma isBigO_of_tendsto_exp_ne_zero {f : ℝ → ℂ} {w : ℂ}
    (hf : ContinuousOn f (Set.Ioi 1))
    (ht : Tendsto (fun s => Complex.exp (f s)) (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 w))
    (hw : w ≠ 0) :
    f =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := by
  have hL' : Tendsto (fun s : ℝ => Complex.exp (f s) / w)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 1) := by
    simpa [div_self hw] using ht.div_const w
  -- On a small interval to the right of `1` the quotient `exp (f s) / w` stays in the right
  -- half-plane, hence in the slit plane.
  have hU : {y : ℂ | (1 : ℝ) / 2 < y.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds (by norm_num)
  have hev : ∀ᶠ s in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      (1 : ℝ) / 2 < (Complex.exp (f s) / w).re := hL'.eventually hU
  obtain ⟨e, he, hesub⟩ := Metric.mem_nhdsWithin_iff.mp hev
  set ε : ℝ := min e 1 / 2 with hεdef
  have hε : 0 < ε := by
    have : 0 < min e 1 := lt_min he one_pos
    linarith
  have hεe : ε < e := by
    have hle : ε ≤ e / 2 := by
      rw [hεdef]
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    linarith [lt_min he one_pos]
  have hε1 : ε < 1 := by
    have hle : ε ≤ 1 / 2 := by
      rw [hεdef]
      exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    linarith
  have hfε : ContinuousOn f (Set.Ioo (1 : ℝ) (1 + ε)) := hf.mono (fun s hs => hs.1)
  have hmemε : ∀ s ∈ Set.Ioo (1 : ℝ) (1 + ε),
      (1 : ℝ) / 2 < (Complex.exp (f s) / w).re := by
    intro s hs
    apply hesub
    refine ⟨?_, hs.1⟩
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : (1 : ℝ) < s := hs.1
    have h2 : s < 1 + ε := hs.2
    rw [abs_of_pos (by linarith : (0 : ℝ) < s - 1)]
    linarith
  set g : ℝ → ℂ := fun s => Complex.log (Complex.exp (f s) / w) + Complex.log w with hgdef
  have hgcont : ContinuousOn g (Set.Ioo (1 : ℝ) (1 + ε)) := by
    have h1 : ContinuousOn (fun s : ℝ => Complex.exp (f s) / w) (Set.Ioo (1 : ℝ) (1 + ε)) :=
      (hfε.cexp).div_const w
    have h2 : ContinuousOn (fun s : ℝ => Complex.log (Complex.exp (f s) / w))
        (Set.Ioo (1 : ℝ) (1 + ε)) :=
      h1.clog (fun s hs => Complex.mem_slitPlane_iff.mpr
        (Or.inl (by linarith [hmemε s hs] : (0 : ℝ) < (Complex.exp (f s) / w).re)))
    simpa [hgdef] using h2.add_const (Complex.log w)
  have hexp : ∀ s ∈ Set.Ioo (1 : ℝ) (1 + ε), Complex.exp (f s) = Complex.exp (g s) := by
    intro s _hs
    have hz : Complex.exp (f s) / w ≠ 0 := div_ne_zero (Complex.exp_ne_zero _) hw
    simp only [hgdef]
    rw [Complex.exp_add, Complex.exp_log hz, Complex.exp_log hw, div_mul_cancel₀ _ hw]
  have hgl : Tendsto g (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 (Complex.log w)) := by
    have h1 : Tendsto (fun s : ℝ => Complex.log (Complex.exp (f s) / w))
        (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 (Complex.log 1)) :=
      hL'.clog (by simp [Complex.mem_slitPlane_iff])
    have := h1.add_const (Complex.log w)
    simpa [hgdef, Complex.log_one] using this
  have hgO : g =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) :=
    hgl.isBigO_one ℂ
  -- The connectedness argument: `f - g` is continuous and `2πiℤ`-valued on `(1, 1+ε)`.
  have hS : IsPreconnected (Set.Ioo (1 : ℝ) (1 + ε)) := isPreconnected_Ioo
  have hFcont : ContinuousOn (fun s : ℝ => f s - g s) (Set.Ioo (1 : ℝ) (1 + ε)) :=
    hfε.sub hgcont
  have hT : IsDiscrete
      (((AddSubgroup.zmultiples (2 * ↑Real.pi * Complex.I) : AddSubgroup ℂ)) : Set ℂ) := by
    rw [isDiscrete_iff_discreteTopology]
    exact NormedSpace.discreteTopology_zmultiples _
  have hmap : Set.MapsTo (fun s : ℝ => f s - g s) (Set.Ioo (1 : ℝ) (1 + ε))
      (((AddSubgroup.zmultiples (2 * ↑Real.pi * Complex.I) : AddSubgroup ℂ)) : Set ℂ) := by
    intro s hs
    have hexps : Complex.exp (f s - g s) = 1 := by
      rw [Complex.exp_sub, hexp s hs, div_self (Complex.exp_ne_zero (g s))]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexps
    change f s - g s ∈ AddSubgroup.zmultiples (2 * ↑Real.pi * Complex.I)
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨n, ?_⟩
    rw [zsmul_eq_mul]
    exact hn.symm
  have hconst : ∀ x ∈ Set.Ioo (1 : ℝ) (1 + ε), ∀ y ∈ Set.Ioo (1 : ℝ) (1 + ε),
      f x - g x = f y - g y :=
    fun x hx y hy => hS.constant_of_mapsTo hT hFcont hmap hx hy
  have hmem : (1 + ε / 2) ∈ Set.Ioo (1 : ℝ) (1 + ε) := by
    refine ⟨?_, ?_⟩ <;> linarith
  have hnb : Set.Ioo (1 : ℝ) (1 + ε) ∈ nhdsWithin (1 : ℝ) (Set.Ioi 1) := by
    rw [Metric.mem_nhdsWithin_iff]
    refine ⟨ε, hε, ?_⟩
    intro s hs
    obtain ⟨hsb, hsi⟩ := hs
    have hs1 : (1 : ℝ) < s := hsi
    have h1 : |s - 1| < ε := by simpa [Real.dist_eq] using (Metric.mem_ball.mp hsb)
    rw [abs_of_pos (by linarith : (0 : ℝ) < s - 1)] at h1
    exact ⟨hs1, by linarith⟩
  have heq : (fun s : ℝ => f s) =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi 1)]
      (fun s : ℝ => g s + (f (1 + ε / 2) - g (1 + ε / 2))) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (1 : ℝ) (1 + ε), hnb, ?_⟩
    intro s hs
    exact sub_eq_iff_eq_add'.mp (hconst s hs _ hmem)
  have hb : (fun s : ℝ => g s + (f (1 + ε / 2) - g (1 + ε / 2)))
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) :=
    hgO.add (isBigO_const_one ℂ (f (1 + ε / 2) - g (1 + ε / 2)) _)
  exact hb.congr' heq.symm Filter.EventuallyEq.rfl

/-- **Non-vanishing of the Artin `L`-series at `s = 1` for a non-trivial character.**

This is the classical non-vanishing input, derived from the two standard ingredients:

* the Euler factorisation `∏_χ L_S(s,χ) = ζ_L^S(s)` over the characters of the abelian group
  `Gal(L/K)` (`NK.HeckeL.Product.prod_artinLSeries_eq_aux`), together with
  `L_S(s,1) = ζ_K^S(s)` (`NK.HeckeL.Product.artinLSeries_one`), which identifies the product of
  the `L`-series of the *non-trivial* characters with the quotient `ζ_L^S(s)/ζ_K^S(s)`;
* the fact that this quotient tends to a *positive* limit
  (`NK.HeckeL.Product.tendsto_zetaUnramified_div`), so no factor of the finite product can
  vanish. -/
lemma lSeries_value_ne_zero_of_regular {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S)
    (h : ∀ ψ : Gal(L/K) →* ℂˣ, ψ ≠ 1 → NK.HeckeL.ArtinLRegularAtOne K L S ψ)
    (χ : Gal(L/K) →* ℂˣ) (hχ : χ ≠ 1) :
    (h χ hχ).value ≠ 0 := by
  classical
  haveI hF : Fintype Gal(L/K) := AlgEquiv.fintype K L
  -- the unramified zeta product of `K` is non-zero, being the Artin `L`-series of the trivial
  -- character, i.e. the exponential of `artinLogEulerProduct`
  have hzne : ∀ s : ℝ, 1 < s → NK.HeckeL.zetaUnramifiedK K S s ≠ 0 := by
    intro s hs hzero
    have h1 : NK.HeckeL.artinLSeries K L S (1 : Gal(L/K) →* ℂˣ) s = 0 := by
      rw [NK.HeckeL.Product.artinLSeries_one]; exact hzero
    have hexp := NK.HeckeL.Series.exp_artinLogEulerProduct (K := K) (L := L) S
      (1 : Gal(L/K) →* ℂˣ) hs
    rw [h1] at hexp
    exact Complex.exp_ne_zero _ hexp
  -- splitting off the trivial character from a finite product
  have hsplit : ∀ f : (Gal(L/K) →* ℂˣ) → ℂ,
      (∏ ψ : Gal(L/K) →* ℂˣ, f ψ)
        = f 1 * ∏ ψ : {ψ : Gal(L/K) →* ℂˣ // ψ ≠ 1}, f ψ.1 := by
    intro f
    have h1 : (∏ ψ : Gal(L/K) →* ℂˣ, f ψ)
        = (∏ ψ ∈ Finset.univ.filter (fun ψ => ψ = 1), f ψ) *
          (∏ ψ ∈ Finset.univ.filter (fun ψ => ¬ ψ = 1), f ψ) :=
      (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun ψ => ψ = 1) f).symm
    rw [h1]
    have h2 : Finset.univ.filter (fun ψ : Gal(L/K) →* ℂˣ => ψ = 1) = {1} := by
      ext ψ; simp
    have h3 : Finset.univ.filter (fun ψ : Gal(L/K) →* ℂˣ => ¬ ψ = 1)
        = Finset.univ.filter (fun ψ => ψ ≠ 1) := rfl
    rw [h2, h3, Finset.prod_singleton]
    congr 1
    exact Finset.prod_subtype (Finset.univ.filter (fun ψ : Gal(L/K) →* ℂˣ => ψ ≠ 1))
      (fun x => by simp [Finset.mem_filter]) f
  -- the product over the non-trivial characters tends to the product of the values
  have hprod_tend : Tendsto
      (fun s : ℝ => ∏ ψ : {ψ : Gal(L/K) →* ℂˣ // ψ ≠ 1},
        NK.HeckeL.artinLSeries K L S ψ.1 s)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (𝓝 (∏ ψ : {ψ : Gal(L/K) →* ℂˣ // ψ ≠ 1}, (h ψ.1 ψ.2).value)) :=
    tendsto_finsetProd Finset.univ (fun ψ _ => (h ψ.1 ψ.2).tendsto)
  -- and it equals the quotient of the unramified zeta products for `s > 1`
  have heq : (fun s : ℝ => ∏ ψ : {ψ : Gal(L/K) →* ℂˣ // ψ ≠ 1},
        NK.HeckeL.artinLSeries K L S ψ.1 s)
      =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi 1)]
      (fun s : ℝ => NK.HeckeL.zetaUnramified K L S s / NK.HeckeL.zetaUnramifiedK K S s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hfull := NK.HeckeL.Product.prod_artinLSeries_eq_aux (K := K) (L := L) S hcomm hS hs
    rw [tprod_fintype] at hfull
    have hsplitf := hsplit (fun ψ => NK.HeckeL.artinLSeries K L S ψ s)
    have hone : NK.HeckeL.artinLSeries K L S (1 : Gal(L/K) →* ℂˣ) s
        = NK.HeckeL.zetaUnramifiedK K S s := NK.HeckeL.Product.artinLSeries_one S s
    have hz := hzne s hs
    have hmain : NK.HeckeL.zetaUnramifiedK K S s *
        (∏ ψ : {ψ : Gal(L/K) →* ℂˣ // ψ ≠ 1}, NK.HeckeL.artinLSeries K L S ψ.1 s)
        = NK.HeckeL.zetaUnramified K L S s := by
      rw [← hone, ← hsplitf]
      exact hfull
    have hgoal : NK.HeckeL.zetaUnramified K L S s / NK.HeckeL.zetaUnramifiedK K S s
        = ∏ ψ : {ψ : Gal(L/K) →* ℂˣ // ψ ≠ 1}, NK.HeckeL.artinLSeries K L S ψ.1 s := by
      rw [← hmain, mul_div_cancel_left₀ _ hz]
    exact hgoal.symm
  -- the quotient has a positive limit
  obtain ⟨c, hcpos, hctend⟩ :=
    NK.HeckeL.Product.tendsto_zetaUnramified_div (K := K) (L := L) S hS
  have hlim : (∏ ψ : {ψ : Gal(L/K) →* ℂˣ // ψ ≠ 1}, (h ψ.1 ψ.2).value) = c :=
    tendsto_nhds_unique hprod_tend (Filter.Tendsto.congr' heq.symm hctend)
  have hne : (∏ ψ : {ψ : Gal(L/K) →* ℂˣ // ψ ≠ 1}, (h ψ.1 ψ.2).value) ≠ 0 := by
    rw [hlim]
    exact Complex.ofReal_ne_zero.mpr hcpos.ne'
  exact (Finset.prod_ne_zero_iff.mp hne) ⟨χ, hχ⟩ (Finset.mem_univ _)

theorem artinPrimeSum_isBigO {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S)
    (h : ∀ ψ : Gal(L/K) →* ℂˣ, ψ ≠ 1 → NK.HeckeL.ArtinLRegularAtOne K L S ψ)
    (χ : Gal(L/K) →* ℂˣ) (hχ : χ ≠ 1) :
    (fun s : ℝ => NK.HeckeL.artinPrimeSum K L S χ s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := by
  -- the value of the `L`-series at `1` is non-zero (non-vanishing input)
  have hv : (h χ hχ).value ≠ 0 := lSeries_value_ne_zero_of_regular S hcomm hS h χ hχ
  -- `artinLogEulerProduct` is a continuous branch of `log (artinLSeries ·)`, whence bounded.
  have hteq : (fun s : ℝ => Complex.exp (NK.HeckeL.artinLogEulerProduct K L S χ s))
      =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun s : ℝ => NK.HeckeL.artinLSeries K L S χ s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact NK.HeckeL.Series.exp_artinLogEulerProduct S χ hs
  have ht : Tendsto (fun s : ℝ => Complex.exp (NK.HeckeL.artinLogEulerProduct K L S χ s))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 (h χ hχ).value) :=
    Filter.Tendsto.congr' hteq.symm (h χ hχ).tendsto
  have hfO : (fun s : ℝ => NK.HeckeL.artinLogEulerProduct K L S χ s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) :=
    isBigO_of_tendsto_exp_ne_zero
      (NK.HeckeL.Series.continuousOn_artinLogEulerProduct S χ) ht hv
  -- `artinPrimeSum` differs from `artinLogEulerProduct` by an `O(1)` term.
  have hsub : (fun s : ℝ => NK.HeckeL.artinPrimeSum K L S χ s -
        NK.HeckeL.artinLogEulerProduct K L S χ s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) :=
    NK.HeckeL.Series.artinPrimeSum_sub_artinLogEulerProduct_isBigO S χ
  have hdecomp : (fun s : ℝ => NK.HeckeL.artinPrimeSum K L S χ s)
      = (fun s : ℝ => NK.HeckeL.artinPrimeSum K L S χ s -
            NK.HeckeL.artinLogEulerProduct K L S χ s)
        + (fun s : ℝ => NK.HeckeL.artinLogEulerProduct K L S χ s) := by
    ext s
    simp only [Pi.add_apply, sub_add_cancel]
  rw [hdecomp]
  exact hsub.add hfO

end NK.HeckeL.Nonvanishing
