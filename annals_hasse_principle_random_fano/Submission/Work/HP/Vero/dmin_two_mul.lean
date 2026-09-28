import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.WedgeDefs
import Submission.Work.HP.tau_basic
import Submission.Work.HP.NA.VeroAux
import Submission.Work.HP.Lat.prim_bezout
import Submission.Work.HP.Lat.gcdMinors2_linear
import Submission.Work.HP.detgam_span_pair_wedgeNorm
import Submission.Work.HP.D2M.wedgeNorm_eq_of_smul_add

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.HP.Vero.D2M

open Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary lattice facts -/

/-- The gcd of the `2 × 2` minors is nonnegative. -/
lemma gcdMinors2_nonneg_int (x y : ι → ℤ) : 0 ≤ gcdMinors2 x y := by
  have h : |gcdMinors2 x y| = gcdMinors2 x y := by
    rw [Int.abs_eq_normalize, gcdMinors2, Finset.normalize_gcd]
  exact h ▸ abs_nonneg _

/-- The rank of the span of an independent pair of integer vectors is two. -/
lemma rk_span_pair (c d : ι → ℤ) (h : LinearIndependent ℤ ![c, d]) :
    rk (Submodule.span ℤ ({c, d} : Set (ι → ℤ))) = 2 := by
  have hrange : (Set.range ![c, d]) = ({c, d} : Set (ι → ℤ)) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hz
      rcases hz with hz | hz
      · exact ⟨0, by simpa using hz.symm⟩
      · exact ⟨1, by simpa using hz.symm⟩
  show Module.finrank ℤ (Submodule.span ℤ ({c, d} : Set (ι → ℤ))) = 2
  rw [← hrange, finrank_span_eq_card h, Fintype.card_fin]

/-- `dmin r S ≤ detL L` for any rank-`r` lattice `L` containing `S`. -/
lemma dmin_le_detL {r : ℕ} {S : Set (ι → ℤ)} {L : Submodule ℤ (ι → ℤ)}
    (hr : rk L = r) (hS : S ⊆ L) : dmin r S ≤ detL L := by
  rw [dmin]
  exact csInf_le ⟨0, fun D ⟨M, _, _, hM⟩ => hM ▸ detL_nonneg M⟩ ⟨L, hr, hS, rfl⟩

/-! ## Scaling of `gcdMinors2` and of `wedgeNorm` -/

/-- `gcdMinors2` scales: `𝒢(g·x, y) = |g| · 𝒢(x, y)`. -/
lemma gcdMinors2_smul_left (g : ℤ) (x y : ι → ℤ) :
    gcdMinors2 (g • x) y = (Int.natAbs g : ℤ) * gcdMinors2 x y := by
  have h := Work.HP.Lat.gcdMinors2_linear x y g 0 0 1
  simpa using h

/-- `wedgeR` scales in its first argument (for nonnegative scalars). -/
lemma wedgeR_smul_left (v w : ι → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    wedgeR (c • v) w = c * wedgeR v w := by
  have h1 : rNorm (c • v) ^ 2 = c ^ 2 * rNorm v ^ 2 := by
    rw [rNorm_sq, rNorm_sq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.smul_apply, smul_eq_mul]; ring
  have h2 : dotR (c • v) w = c * dotR v w := Work.HP.D2M.dotR_smul_left' c v w
  have hid : c ^ 2 * rNorm v ^ 2 * rNorm w ^ 2 - (c * dotR v w) ^ 2
      = c ^ 2 * (rNorm v ^ 2 * rNorm w ^ 2 - dotR v w ^ 2) := by ring
  simp only [wedgeR, h1, h2, hid, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hc]

/-- `wedgeNorm` scales in its first argument (for nonnegative integer scalars). -/
lemma wedgeNorm_smul_left (x y : ι → ℤ) (g : ℤ) (hg : 0 ≤ g) :
    wedgeNorm (g • x) y = (g : ℝ) * wedgeNorm x y := by
  have ht : toR (g • x) = (g : ℝ) • toR x := by
    ext i
    simp only [toR, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [wedgeNorm_eq_wedgeR, ht, wedgeR_smul_left _ _ _ (by exact_mod_cast hg),
    ← wedgeNorm_eq_wedgeR]

/-! ## The Bézout lemma for primitive vectors -/

/-- For a primitive `x`, the vector `y` is a multiple of `x` modulo `𝒢(x,y)`: there is an integer
`k` with `𝒢(x,y) ∣ y i - k * x i` for all `i`.

Indeed, if `∑ i, u i * x i = 1` (`Lat.prim_bezout`), take `k = ∑ i, u i * y i`; then
`y j - k * x j = ∑ i, u i * (x i * y j - x j * y i)` is a combination of `2 × 2` minors. -/
theorem exists_k_of_prim (x y : ι → ℤ) (hx : IsPrim x) :
    ∃ k : ℤ, ∀ i, gcdMinors2 x y ∣ (y i - k * x i) := by
  classical
  obtain ⟨u, hu⟩ := Work.HP.Lat.prim_bezout x hx
  refine ⟨∑ i, u i * y i, fun j => ?_⟩
  have hminor : ∀ i, gcdMinors2 x y ∣ (x i * y j - x j * y i) :=
    fun i => ((Work.HP.NA.gcdMinors2_dvd_iff (gcdMinors2 x y) x y).mp dvd_rfl) i j
  have hsum : gcdMinors2 x y ∣ ∑ i, u i * (x i * y j - x j * y i) :=
    Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (hminor i) (u i))
  have hkey : ∑ i, u i * (x i * y j - x j * y i)
      = y j - (∑ i, u i * y i) * x j := by
    have e1 : ∀ i, u i * (x i * y j - x j * y i)
        = (u i * x i) * y j - (u i * y i) * x j := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.sum_mul, hu]
    ring
  rw [hkey] at hsum
  exact hsum

/-! ## Dividing a nonzero vector by its gcd -/

/-- The gcd of the entries of an integer vector is nonnegative. -/
lemma int_finset_gcd_nonneg (x : ι → ℤ) : 0 ≤ Finset.univ.gcd x := by
  have h : |Finset.univ.gcd x| = Finset.univ.gcd x := by
    rw [Int.abs_eq_normalize, Finset.normalize_gcd]
  exact h ▸ abs_nonneg _

/-- Dividing a nonzero integer vector by the gcd `g` of its entries produces a primitive vector
`x'` with `g • x' = x`. -/
theorem gcd_div_prim (x : ι → ℤ) (hx : x ≠ 0) :
    (0 : ℤ) < Finset.univ.gcd x ∧ IsPrim (fun i => x i / Finset.univ.gcd x) ∧
      Finset.univ.gcd x • (fun i => x i / Finset.univ.gcd x) = x := by
  classical
  set g : ℤ := Finset.univ.gcd x with hgdef
  have hg0 : 0 ≤ g := by rw [hgdef]; exact int_finset_gcd_nonneg x
  have hgne : g ≠ 0 := by
    intro h0
    apply hx
    funext i
    exact Finset.gcd_eq_zero_iff.mp (by rw [← hgdef]; exact h0) i (Finset.mem_univ i)
  have hdvd : ∀ i, g ∣ x i := fun i => by
    rw [hgdef]; exact Finset.gcd_dvd (Finset.mem_univ i)
  refine ⟨lt_of_le_of_ne hg0 (Ne.symm hgne), ?_, ?_⟩
  · rw [IsPrim]
    have h1 : Finset.univ.gcd (fun i => g * (x i / g)) = g := by
      rw [Finset.gcd_congr rfl (fun i _ => Int.mul_ediv_cancel' (hdvd i)), hgdef]
    have h2 := Finset.gcd_mul_left (s := Finset.univ) (f := fun i => x i / g) (a := g)
    rw [h1] at h2
    have h3 : normalize g = g := by rw [← Int.abs_eq_normalize, abs_of_nonneg hg0]
    rw [h3] at h2
    have h4 : g * Finset.univ.gcd (fun i => x i / g) = g * 1 := by rw [mul_one, ← h2]
    exact mul_left_cancel₀ hgne h4
  · funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Int.mul_ediv_cancel' (hdvd i)

/-! ## The primitive case -/

/-- For a primitive `x` and a `ℤ`-independent `y` there is a rank-`2` lattice containing both
`x` and `y` whose determinant times `𝒢(x,y)` is `wedgeNorm x y`. -/
theorem exists_pair_lat (x y : ι → ℤ) (hx : IsPrim x) (hxy : LinearIndependent ℤ ![x, y]) :
    ∃ L : Submodule ℤ (ι → ℤ), rk L = 2 ∧ x ∈ L ∧ y ∈ L ∧
      detL L * (gcdMinors2 x y : ℝ) = wedgeNorm x y := by
  classical
  obtain ⟨k, hk⟩ := exists_k_of_prim x y hx
  set G : ℤ := gcdMinors2 x y with hGdef
  have hG0 : 0 ≤ G := by rw [hGdef]; exact gcdMinors2_nonneg_int x y
  have hGne : G ≠ 0 := by
    intro h0
    have hyk : y = k • x := by
      funext i
      have h := hk i
      rw [h0] at h
      obtain ⟨c, hc⟩ := h
      simp only [zero_mul] at hc
      simpa only [Pi.smul_apply, smul_eq_mul] using sub_eq_zero.mp hc
    have hrel : k • x + (-1 : ℤ) • y = 0 := by
      rw [hyk, smul_smul]
      norm_num
    obtain ⟨h1, h2⟩ := (LinearIndependent.pair_iff.mp hxy) k (-1) hrel
    norm_num at h2
  let w : ι → ℤ := fun i => (y i - k * x i) / G
  have hw : ∀ i, G * w i = y i - k * x i := fun i => Int.mul_ediv_cancel' (hk i)
  have hyvec : y = k • x + G • w := by
    funext i
    have h := hw i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hli : LinearIndependent ℤ ![x, w] := by
    rw [LinearIndependent.pair_iff] at hxy ⊢
    intro a b hab
    have hcoord : ∀ i, (G * a - b * k) * x i + b * y i = 0 := by
      intro i
      have h1 := congrFun hab i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
      have h2 : y i = k * x i + G * w i := by
        have h := hw i; linarith
      linear_combination G * h1 + b * h2
    have hrel : (G * a - b * k) • x + b • y = 0 := by
      funext i
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hcoord i
    obtain ⟨hcoef, hb0⟩ := hxy (G * a - b * k) b hrel
    refine ⟨?_, hb0⟩
    rw [hb0] at hcoef
    exact (mul_eq_zero.mp (by simpa using hcoef)).resolve_left hGne
  refine ⟨Submodule.span ℤ ({x, w} : Set (ι → ℤ)), rk_span_pair x w hli, ?_, ?_, ?_⟩
  · exact Submodule.subset_span (by simp)
  · rw [hyvec]
    exact Submodule.add_mem _ (Submodule.smul_mem _ k (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ G (Submodule.subset_span (by simp)))
  · have hwedge : wedgeNorm x y = (G : ℝ) * wedgeNorm x w := by
      rw [hyvec]
      exact Work.HP.D2M.wedgeNorm_eq_of_smul_add x w k G hG0
    rw [detgam_span_pair_wedgeNorm x w hli, hwedge]
    ring

end Work.HP.Vero.D2M

namespace Work.HP.Vero

open Work.HP

/-- The easy direction of the paper's "Lemma d₂(x,y)", in division-free form: for `ℤ`-linearly
independent `x, y`, `𝔡₂(x,y) · 𝒢(x,y) ≤ wedgeNorm x y`.

NOTE FOR THE PROVER: this module must NOT import `Submission.Work.HP.numaux.Defs` or any module
that imports it.  `Submission.Work.HP.Vero` and `Submission.Work.HP.numaux.Defs` both define
`Work.HP.orthLat`, so a file importing both fails with "environment already contains
`Work.HP.orthLat`"; the caller imports `Submission.Work.HP.Vero`, so this file must not (so for
instance `Submission.Work.HP.det_gam` and `Submission.Work.HP.Vero.dmin_two_le`, which do, cannot
be used here).  Suggested route avoiding `satLat`: let `𝒢 = gcdMinors2 x y` and use
`HP/NA/exists_lam_gcdMinors2` (locally `p^e ∣ 𝒢 ⟹ ∃c, ∀j, p^e ∣ y j - c * x j`) to find `k : ℤ`
with `𝒢 ∣ y i - k * x i` for all `i` (combine over the prime powers dividing `𝒢`, using
`𝒢 ∣ x i * y j - x j * y i` for `i = i₀` with `gcd x = 1`), set `w i = (y i - k * x i) / 𝒢`, so that
`y = k • x + 𝒢 • w`; then `L := span ℤ {x, w}` is a rank-two lattice containing `x` and `y`, hence
`dmin 2 {x,y} ≤ detL L = wedgeNorm x w`, and
`(wedgeNorm x w) * 𝒢 = wedgeNorm x y` by the Gram identity. -/
theorem dmin_two_mul {n : ℕ} (x y : Fin (n + 1) → ℤ) (hxy : LinearIndependent ℤ ![x, y]) :
    dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * (gcdMinors2 x y : ℝ) ≤ wedgeNorm x y := by
  classical
  have hx0 : x ≠ 0 := hxy.ne_zero 0
  obtain ⟨hgpos, hprim, hsplit⟩ := D2M.gcd_div_prim x hx0
  let g : ℤ := Finset.univ.gcd x
  let x' : Fin (n + 1) → ℤ := fun i => x i / Finset.univ.gcd x
  have hgnz : g ≠ 0 := ne_of_gt hgpos
  have hsplit' : g • x' = x := by simpa only [g, x'] using hsplit
  have hli' : LinearIndependent ℤ ![x', y] := by
    rw [LinearIndependent.pair_iff] at hxy ⊢
    intro a b hab
    have hcoord : ∀ i, a * x i + (g * b) * y i = 0 := by
      intro i
      have h1 := congrFun hab i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
      have h2 := congrFun hsplit' i
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      rw [← h2]
      linear_combination g * h1
    have hrel : a • x + (g * b) • y = 0 := by
      funext i
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hcoord i
    obtain ⟨ha, hgb⟩ := hxy a (g * b) hrel
    exact ⟨ha, by rcases mul_eq_zero.mp hgb with h | h; exacts [absurd h hgnz, h]⟩
  obtain ⟨L, hrk, hxL, hyL, hdet⟩ := D2M.exists_pair_lat x' y hprim hli'
  have hxL' : x ∈ L := by rw [← hsplit']; exact L.smul_mem g hxL
  have hsub : ({x, y} : Set (Fin (n + 1) → ℤ)) ⊆ L := by
    intro z hz
    rcases hz with h | h
    · rw [h]; exact hxL'
    · rw [h]; exact hyL
  have hle : dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ≤ detL L := D2M.dmin_le_detL hrk hsub
  have hG : (gcdMinors2 x y : ℝ) = (g : ℝ) * (gcdMinors2 x' y : ℝ) := by
    have h1 := D2M.gcdMinors2_smul_left g x' y
    have h2 : (Int.natAbs g : ℤ) = g := Int.natAbs_of_nonneg (le_of_lt hgpos)
    rw [hsplit', h2] at h1
    exact_mod_cast h1
  have hW : wedgeNorm x y = (g : ℝ) * wedgeNorm x' y := by
    rw [← hsplit']
    exact D2M.wedgeNorm_smul_left x' y g (le_of_lt hgpos)
  have hnn : (0 : ℝ) ≤ (gcdMinors2 x y : ℝ) := by
    rw [hG]
    exact mul_nonneg (by exact_mod_cast le_of_lt hgpos)
      (by exact_mod_cast D2M.gcdMinors2_nonneg_int x' y)
  calc dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * (gcdMinors2 x y : ℝ)
      ≤ detL L * (gcdMinors2 x y : ℝ) := mul_le_mul_of_nonneg_right hle hnn
    _ = detL L * ((g : ℝ) * (gcdMinors2 x' y : ℝ)) := by rw [hG]
    _ = (g : ℝ) * (detL L * (gcdMinors2 x' y : ℝ)) := by ring
    _ = (g : ℝ) * wedgeNorm x' y := by rw [hdet]
    _ = wedgeNorm x y := hW.symm

end Work.HP.Vero
