import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.asmDefs

/-!
# Colours missing a vertex, in terms of the leftover objects (the `(ii)_j` register)

`objCover` bounds the number of colours missing `w` by the number of "missing
degrees" of `w` plus the number of unused objects through `w`; with the degree
regularity `(1 ± βp) D` and NB3's `γp |F| + κ max(|F|, D)` this is at most
`(γp + 2κ) D`.
-/

set_option autoImplicit false

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

theorem ncard_miss_objVert_le {n D : ℕ} {𝓜 : MultiHypergraph n}
    {βp κ γp : ℝ} (N : Fin D → Set (EdgeObj 𝓜)) (w : Fin n)
    (hmatch : ∀ i, IsObjMatching (N i))
    (hleft : ∀ F ∈ ({objThrough 𝓜 w | w : Fin n} : Set (Set (EdgeObj 𝓜))),
      (({x ∈ F | ∀ c : Fin D, x ∉ N c}).ncard : ℝ) ≤
        γp * (F.ncard : ℝ) + κ * max (F.ncard : ℝ) (D : ℝ))
    (hdegw : |((𝓜.deg w : ℝ)) - (D : ℝ)| ≤ βp * (D : ℝ))
    (hγp0 : 0 ≤ γp) (hκ0 : 0 ≤ κ) (hβp0 : 0 ≤ βp)
    (hβpκ : 10 * βp ≤ κ) (hγp1 : γp ≤ 1) (hκ1 : κ ≤ 1) :
    (({c : Fin D | w ∉ objVert (N c)} : Set (Fin D)).ncard : ℝ) ≤
      (γp + 2 * κ) * (D : ℝ) := by
  classical
  have hcov := objCover N hmatch w
  have hmem : objThrough 𝓜 w ∈ ({objThrough 𝓜 w | w : Fin n} : Set (Set (EdgeObj 𝓜))) :=
    ⟨w, rfl⟩
  have hL := hleft _ hmem
  have hdegR : ((objThrough 𝓜 w).ncard : ℝ) = (𝓜.deg w : ℝ) := by
    rw [objThrough_ncard]
  rw [hdegR] at hL
  set m : ℝ := (𝓜.deg w : ℝ) with hmdef
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  have habs := hdegw
  rw [abs_le] at habs
  have h1 : (D : ℝ) - m ≤ βp * (D : ℝ) := by linarith [habs.1]
  have h2 : m ≤ (1 + βp) * (D : ℝ) := by linarith [habs.2]
  have h3 : max m (D : ℝ) ≤ (1 + βp) * (D : ℝ) := by
    refine max_le h2 ?_
    linarith [hβp0, hD0]
  have hβp1 : βp ≤ κ / 10 := by linarith
  have hb2 : γp * βp ≤ κ / 10 := by nlinarith [hβp1, hγp1, hκ0, hγp0]
  have hb3 : κ * βp ≤ κ / 10 := by nlinarith [hβp1, hκ1, hκ0]
  have hkey : βp + γp * βp + κ * βp ≤ κ := by linarith
  nlinarith [hcov, hL, h1, h2, h3, hkey, hm0, hγp0, hκ0, hD0]

end Work.Deep.Nibble
