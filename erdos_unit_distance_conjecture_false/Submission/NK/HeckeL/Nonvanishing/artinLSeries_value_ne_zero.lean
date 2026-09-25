import Mathlib
import Submission.NK.HeckeL.Zeta
import Submission.NK.HeckeL.Product.artinLSeries_one
import Submission.NK.HeckeL.Product.prod_artinLSeries_eq
import Submission.NK.HeckeL.Product.tendsto_zetaUnramified_div

open scoped BigOperators Topology
open Filter

namespace NK.HeckeL.Nonvanishing

/-- Splitting a finite product over a group along the neutral element: the product over the
non-trivial characters times the trivial factor is the full product. -/
lemma prod_ne_one_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ℂ) (a : ι) :
    (∏ x : {x // x ≠ a}, F x.1) * F a = ∏ x, F x := by
  classical
  rw [← Finset.prod_erase_mul Finset.univ F (Finset.mem_univ a)]
  congr 1
  exact (Finset.prod_subtype (Finset.univ.erase a) (by intro x; simp) F).symm

/-- **The Artin `L`-series of a non-trivial character does not vanish at `s = 1`.**

Under the standing hypothesis that for every non-trivial character `ψ` of the abelian extension
`L/K` the Artin `L`-series `L(s, ψ)` has a finite limit `(h ψ hψ).value` as `s → 1⁺`, the value
attached to a non-trivial character is non-zero.

The proof is the classical one.  For `s > 1` the product formula
`∏_ψ L(s, ψ) = zetaUnramified K L S s` (Euler factors: a prime `𝔭 ∉ S` contributes the
`|Gal|/ord`-th power of the factorisation of `L` over `𝔭`), together with the trivial-character
identity `L(s, 1) = zetaUnramifiedK K S s`, shows that the product of the non-trivial `L`-series is
the quotient of the two truncated Dedekind zeta products; that quotient has a *positive* limit at
`s = 1⁺` (both truncated products have a simple pole there, the ratio of the residues being
positive).  Since the product of the finitely many non-trivial `L`-series also tends to the product
of their values, that product of values is non-zero, and hence so is each factor. -/
theorem artinLSeries_value_ne_zero {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S)
    (h : ∀ ψ : Gal(L/K) →* ℂˣ, ψ ≠ 1 → NK.HeckeL.ArtinLRegularAtOne K L S ψ)
    (χ : Gal(L/K) →* ℂˣ) (hχ : χ ≠ 1) :
    (h χ hχ).value ≠ 0 := by
  classical
  -- The quotient of the two truncated Euler products has a positive limit at `s → 1⁺`.
  obtain ⟨c, hcpos, hc⟩ :=
    NK.HeckeL.Product.tendsto_zetaUnramified_div (K := K) (L := L) S hS
  have hcne : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
  -- The unramified zeta product is eventually non-zero (otherwise the quotient, which tends to
  -- the non-zero value `c`, would vanish at points arbitrarily close to `1`).
  have hZK : ∀ᶠ s in (nhdsWithin (1 : ℝ) (Set.Ioi 1)),
      NK.HeckeL.zetaUnramifiedK K S s ≠ 0 := by
    have h := hc.eventually (eventually_ne_nhds hcne)
    filter_upwards [h] with s hs
    intro h0
    exact hs (by rw [h0, div_zero])
  -- On `s > 1` the product of the non-trivial `L`-series is the quotient of the two products.
  have hmain : ∀ᶠ s in (nhdsWithin (1 : ℝ) (Set.Ioi 1)),
      (∏ ψ : {ψ : Gal(L/K) →* ℂˣ // ψ ≠ 1}, NK.HeckeL.artinLSeries K L S ψ.1 s) =
        NK.HeckeL.zetaUnramified K L S s / NK.HeckeL.zetaUnramifiedK K S s := by
    filter_upwards [self_mem_nhdsWithin, hZK] with s hs hZKs
    have hs1 : (1 : ℝ) < s := hs
    have hprod : (∏ ψ : Gal(L/K) →* ℂˣ, NK.HeckeL.artinLSeries K L S ψ s) =
        NK.HeckeL.zetaUnramified K L S s := by
      simpa using NK.HeckeL.Product.prod_artinLSeries_eq (K := K) (L := L) S hcomm hS hs1
    have hsplit := prod_ne_one_mul
      (fun ψ : Gal(L/K) →* ℂˣ => NK.HeckeL.artinLSeries K L S ψ s) 1
    rw [← hsplit, NK.HeckeL.Product.artinLSeries_one S s] at hprod
    rw [eq_div_iff hZKs]
    exact hprod
  -- The product over the non-trivial characters tends to the product of the values.
  have hlim1 : Tendsto (fun s : ℝ =>
      ∏ ψ : {ψ : Gal(L/K) →* ℂˣ // ψ ≠ 1}, NK.HeckeL.artinLSeries K L S ψ.1 s)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (𝓝 (∏ ψ : {ψ : Gal(L/K) →* ℂˣ // ψ ≠ 1}, (h ψ.1 ψ.2).value)) := by
    have hb := tendsto_finset_prod (Finset.univ : Finset {ψ : Gal(L/K) →* ℂˣ // ψ ≠ 1})
      (f := fun (ψ : {ψ : Gal(L/K) →* ℂˣ // ψ ≠ 1}) (s : ℝ) =>
        NK.HeckeL.artinLSeries K L S ψ.1 s)
      (a := fun ψ => (h ψ.1 ψ.2).value) (x := nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (fun ψ _ => (h ψ.1 ψ.2).tendsto)
    simpa using hb
  -- Comparing the two limits.
  have hlim2 : Tendsto (fun s : ℝ =>
      NK.HeckeL.zetaUnramified K L S s / NK.HeckeL.zetaUnramifiedK K S s)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (𝓝 (∏ ψ : {ψ : Gal(L/K) →* ℂˣ // ψ ≠ 1}, (h ψ.1 ψ.2).value)) := hlim1.congr' hmain
  have heq : (∏ ψ : {ψ : Gal(L/K) →* ℂˣ // ψ ≠ 1}, (h ψ.1 ψ.2).value) = (c : ℂ) :=
    tendsto_nhds_unique hlim2 hc
  have hne : (∏ ψ : {ψ : Gal(L/K) →* ℂˣ // ψ ≠ 1}, (h ψ.1 ψ.2).value) ≠ 0 := by
    rw [heq]; exact hcne
  intro h0
  exact hne (Finset.prod_eq_zero
    (s := Finset.univ) (f := fun ψ : {ψ : Gal(L/K) →* ℂˣ // ψ ≠ 1} => (h ψ.1 ψ.2).value)
    (Finset.mem_univ ⟨χ, hχ⟩) h0)

end NK.HeckeL.Nonvanishing
