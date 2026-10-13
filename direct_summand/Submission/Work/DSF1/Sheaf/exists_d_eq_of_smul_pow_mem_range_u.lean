import Mathlib
import Submission.Work.DSF1.Sheaf.CechStruct
import Submission.Work.DSF1.Sheaf.exists_d_eq_of_smul_pow_mem_range

universe u

namespace Work.DSF1.Sheaf

/-- Universe-polymorphic variant of `exists_d_eq_of_smul_pow_mem_range`: if multiplication
by `g` is bijective on every term of a cochain complex `K` of `R`-modules, then a class
`s` lies in the image of `d^n` as soon as some `g`-power multiple of it does. -/
theorem exists_d_eq_of_smul_pow_mem_range_u {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (g : R)
    (hg : ∀ m, Function.Bijective (fun x : K.X m => g • x))
    (n : ℕ) (s : K.X (n + 1)) (k : ℕ)
    (hs : g ^ k • s ∈ LinearMap.range (K.d n (n + 1)).hom) :
    ∃ t : K.X n, (K.d n (n + 1)).hom t = s := by
  -- `im(d^n)` is closed under multiplication by `g⁻¹` on `K.X (n+1)`.
  have hkey : ∀ y : K.X (n + 1),
      g • y ∈ LinearMap.range (K.d n (n + 1)).hom →
      y ∈ LinearMap.range (K.d n (n + 1)).hom := by
    intro y hy
    obtain ⟨c, hc⟩ := hy
    obtain ⟨t', ht'⟩ := (hg n).2 c
    have htg : g • t' = c := ht'
    refine ⟨t', ?_⟩
    have h1 : g • y = g • (K.d n (n + 1)).hom t' := by
      calc g • y = (K.d n (n + 1)).hom c := hc.symm
        _ = (K.d n (n + 1)).hom (g • t') := by rw [htg]
        _ = g • (K.d n (n + 1)).hom t' := LinearMap.map_smul _ g t'
    exact ((hg (n + 1)).1 h1).symm
  -- Repeatedly strip off powers of `g`.
  have hpow : ∀ k, g ^ k • s ∈ LinearMap.range (K.d n (n + 1)).hom →
      s ∈ LinearMap.range (K.d n (n + 1)).hom := by
    intro k
    induction k with
    | zero => intro h; simpa using h
    | succ k ih =>
      intro h
      apply ih
      apply hkey
      have he : g • (g ^ k • s) = g ^ (k + 1) • s := by
        rw [smul_smul, pow_succ']
      rwa [he]
  obtain ⟨t, ht⟩ := hpow k hs
  exact ⟨t, ht⟩

end Work.DSF1.Sheaf
