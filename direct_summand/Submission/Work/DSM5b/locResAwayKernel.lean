import Mathlib
import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5b.awayKernel_pow_mul
import Submission.Work.DSM5b.prod_dvd_mul_of_subset_insert

namespace Work.DSM5b

universe a

/-- **A `W`-algebra map out of `W_s` kills `tk`-torsion only, when `s * tk = c * w`.**

General form of the argument, with the localisation `W_c` and the algebra map `φ : W_s →ₐ[W] W_c`
kept abstract: if `φ x = φ y` for `x y ∈ W_s` and `s * tk = c * w`, then `x` and `y` agree in
`W_s` after multiplication by a power of the image of `tk`.

Route: write `x` and `y` over a common denominator `s^N` (`IsLocalization.Away.surj`, taking the
maximum of the two exponents and multiplying the numerators by the missing powers).  Applying `φ`
and using `φ (algebraMap W _ r) = algebraMap W _ r` turns `φ x = φ y` into the equality of the
numerators in `W_c`, so `IsLocalization.Away.exists_of_eq c` produces `m` with `c^m * a = c^m * b`
in `W`.  Multiplying by `w^m` (so that `(c w)^m = (s tk)^m`), mapping to `W_s` and cancelling the
units `s^m`, `s^N` is `Work.DSM5b.awayKernel_pow_mul`. -/
theorem awayAlgHom_eq_pow_mul {W : Type a} [CommRing W] {s c tk w : W} (hc : s * tk = c * w)
    (φ : Localization.Away s →ₐ[W] Localization.Away c) (x y : Localization.Away s)
    (hxy : φ x = φ y) :
    ∃ n : ℕ, (algebraMap W (Localization.Away s) tk) ^ n * x =
      (algebraMap W (Localization.Away s) tk) ^ n * y := by
  obtain ⟨N₁, a₁, ha₁⟩ := IsLocalization.Away.surj s x
  obtain ⟨N₂, b₁, hb₁⟩ := IsLocalization.Away.surj s y
  have hN₁ : N₁ ≤ max N₁ N₂ := le_max_left _ _
  have hN₂ : N₂ ≤ max N₁ N₂ := le_max_right _ _
  have ha : x * (algebraMap W (Localization.Away s) s) ^ (max N₁ N₂) =
      algebraMap W (Localization.Away s) (a₁ * s ^ (max N₁ N₂ - N₁)) := by
    rw [map_mul, map_pow, ← ha₁, mul_assoc, ← pow_add, Nat.add_sub_cancel' hN₁]
  have hb : y * (algebraMap W (Localization.Away s) s) ^ (max N₁ N₂) =
      algebraMap W (Localization.Away s) (b₁ * s ^ (max N₁ N₂ - N₂)) := by
    rw [map_mul, map_pow, ← hb₁, mul_assoc, ← pow_add, Nat.add_sub_cancel' hN₂]
  have h1 := congrArg φ ha
  have h2 := congrArg φ hb
  simp only [map_mul, map_pow, AlgHom.commutes] at h1 h2
  have key : (algebraMap W (Localization.Away c)) a₁ *
        (algebraMap W (Localization.Away c)) s ^ (max N₁ N₂ - N₁) =
      (algebraMap W (Localization.Away c)) b₁ *
        (algebraMap W (Localization.Away c)) s ^ (max N₁ N₂ - N₂) := by
    rw [← h1, ← h2, hxy]
  have key' : (algebraMap W (Localization.Away c)) (a₁ * s ^ (max N₁ N₂ - N₁)) =
      (algebraMap W (Localization.Away c)) (b₁ * s ^ (max N₁ N₂ - N₂)) := by
    simpa only [map_mul, map_pow] using key
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq c key'
  exact ⟨m, awayKernel_pow_mul s c tk w hc ha hb hm⟩

/-- **The kernel of the chart localisation map `W_{t_S} → W_{t_T}` is `t k`-torsion.**

Let `W` be a commutative ring, `t : ι → W`, and `S ⊆ T` finsets of indices with `T ⊆ insert k S`
(so `T = S` or `T = S ∪ {k}`), so that `tS t T ∣ tS t S * t k`.  Then two elements of
`W_{t_S} = Localization.Away (tS t S)` with the same image under `locRes t hST : W_{t_S} → W_{t_T}`
agree after multiplication by a power of `t k`.

Route: since `tS t T ∣ tS t (insert k S)` (`tS_dvd` from `T ⊆ insert k S`) and
`tS t (insert k S) ∣ tS t S * t k` (`Finset.prod_insert` when `k ∉ S`, and `insert k S = S` when
`k ∈ S`), fix `h` with `tS t S * t k = tS t T * h`.  Use `IsLocalization.Away.surj` twice to write
`x * (algebraMap W _ (tS t S)) ^ N = algebraMap W _ a` and
`y * (algebraMap W _ (tS t S)) ^ N = algebraMap W _ b` with a common `N` (take the maximum of the
two exponents and multiply by the remaining powers).  Applying `locRes t hST` and using
`AlgHom.commutes`, the hypothesis gives `algebraMap W _ (tS t T) a = algebraMap W _ (tS t T) b`, so by
`IsLocalization.eq_iff_exists (Submonoid.powers (tS t T))` there is `m` with
`(tS t T) ^ m * a = (tS t T) ^ m * b` in `W`.  Multiplying by `h ^ m` gives
`(tS t S * t k) ^ m * a = (tS t S * t k) ^ m * b` in `W`, and mapping this to `W_{t_S}`, where
`algebraMap W _ (tS t S)` is a unit, and cancelling the units `(algebraMap W _ (tS t S)) ^ m` and
`(algebraMap W _ (tS t S)) ^ N` yields
`(algebraMap W _ (t k)) ^ m * x = (algebraMap W _ (t k)) ^ m * y`.  The argument is uniform in `k`
(it never uses `k ∉ S`), and needs no hypothesis on `t k`: if `tS t T = 0` then the case `m = 0`
gives `a = b` whence `x = y` directly, and the case `m ≥ 1` gives the claim. -/
theorem locResAwayKernel {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    {S T : Finset ι} (hST : S ⊆ T) {k : ι} (hT : T ⊆ insert k S)
    (x y : Localization.Away (DSMap.Mix2.tS t S))
    (h : (DSMap.Mix2.locRes t hST x : Localization.Away (DSMap.Mix2.tS t T)) =
      DSMap.Mix2.locRes t hST y) :
    ∃ n : ℕ, (algebraMap W (Localization.Away (DSMap.Mix2.tS t S)) (t k)) ^ n * x =
      (algebraMap W (Localization.Away (DSMap.Mix2.tS t S)) (t k)) ^ n * y := by
  -- `tS t T ∣ tS t S * t k`, i.e. `tS t S * t k = tS t T * w` for some `w : W`.
  obtain ⟨w, hw⟩ :=
    dvd_def.mp (prod_dvd_mul_of_subset_insert (M := W) t hST hT)
  exact awayAlgHom_eq_pow_mul (s := DSMap.Mix2.tS t S) (c := DSMap.Mix2.tS t T)
    (tk := t k) (w := w) hw (DSMap.Mix2.locRes t hST) x y h

end Work.DSM5b
