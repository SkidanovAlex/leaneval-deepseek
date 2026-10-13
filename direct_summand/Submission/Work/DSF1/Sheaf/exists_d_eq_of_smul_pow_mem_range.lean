import Mathlib

namespace Work.DSF1.Sheaf

/-- If multiplication by `g` is bijective on every term of a cochain complex `K` of
`R`-modules, then the differentials are "`g`-localized isomorphisms": a class `s` lies in
the image of `d^n` as soon as some `g`-power multiple of it does.

Indeed `im(d^n) ⊆ K.X (n+1)` is stable under multiplication by `g` and (because `g` is
invertible on `K.X (n+1)` and `g` commutes with `d`) also under multiplication by `g⁻¹`;
hence multiplication by `g` restricts to an automorphism of `im(d^n)`. -/
theorem exists_d_eq_of_smul_pow_mem_range {R : Type} [CommRing R]
    (K : CochainComplex (ModuleCat R) ℕ) (g : R)
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
