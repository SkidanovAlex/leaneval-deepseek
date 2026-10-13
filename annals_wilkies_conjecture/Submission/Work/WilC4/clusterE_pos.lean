/-
  WilC4/clusterE_pos : the cluster exponent set `Route.ClusterE Y B` of the ULPM route is
  **non-empty in the positive part**.

  ## Why this is true and what it uses

  `Route.ClusterE Y B` is the set of `ρ` for which, at every natural scale `B ≥ 1`, there are a
  parameter `c` and a positive `B`-deep point `x` such that the doubling ratio `f_c(2t)/f_c(t)` of
  the fibre stays within `1/B` of `ρ` on the whole window `[x/B, xB]`.

  The positive element is produced from the polynomial boundedness hypothesis `hPB`, which is the
  only global *analytic* input available about the family `Y`:

  * `C0_rexp_syntax_proved hR` turns the `LRc`-definability of `Y` (`hY`) into `RExpExist Y`, so
    that `hPB` applies to `Y` (`hfun` says `Y` is a family of graphs);
  * `hPB` then gives, for every parameter `c`, the dichotomy "the fibre of `c` is eventually `0`,
    or asymptotic to `a x^q` (`q ∈ ℚ`, `a ≠ 0`) at `+∞";
  * the first alternative is impossible: `B_c` is finite (`hBcard`), so above all breakpoints one
    finds an interval avoiding `B_c`, on which `GoodFibre` (`hgf`) makes the fibre everywhere
    defined and non-zero, contradicting "eventually `0`";
  * in the second alternative, `ρ := 2^q > 0` is a cluster value: for a scale `N`, take any
    `x` larger than `N·R` and than `2N·(max B_c)` (so that `x` is `N`-deep and the whole window
    lies beyond the asymptotic threshold `R`); on the window
    `|f_c(2t)/f_c(t) − 2^q| ≤ 2^q · 4ε/|a| ≤ 1/N` by the two asymptotic bounds at `t` and `2t`.

  The three private arithmetic lemmas below carry the `ε`-bookkeeping.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ErealDefs
import Submission.Work.WilC4.ULPMExp

namespace Work.WilC4

/-- If `u` and `v` are both within `ε` of `a` and `ε ≤ |a|/2`, then `u/v` is within `4ε/|a|` of
`1`.  (The `ε`-bookkeeping of "two asymptotically equal quantities have ratio `→ 1`".) -/
private lemma abs_div_sub_one_le {u v a ε : ℝ} (hv : v ≠ 0) (hu : |u - a| < ε)
    (hva : |v - a| < ε) (hε : ε ≤ |a| / 2) : |u / v - 1| ≤ 4 * ε / |a| := by
  have hεpos : 0 < ε := lt_of_le_of_lt (abs_nonneg _) hu
  have hle : |a| ≤ |v| + ε := by
    calc |a| = |v + (a - v)| := by ring_nf
      _ ≤ |v| + |a - v| := abs_add_le _ _
      _ = |v| + |v - a| := by rw [abs_sub_comm]
      _ ≤ |v| + ε := by linarith
  have ha : 0 < |a| := by linarith
  have hvabs : |a| / 2 ≤ |v| := by linarith
  have h2ε : |u - v| ≤ 2 * ε := by
    have h3 : |u - v| ≤ |u - a| + |a - v| := by
      calc |u - v| = |(u - a) + (a - v)| := by ring_nf
        _ ≤ |u - a| + |a - v| := abs_add_le _ _
    have h4 : |a - v| = |v - a| := abs_sub_comm a v
    linarith
  have hkey : u / v - 1 = (u - v) / v := by field_simp
  rw [hkey, abs_div]
  have hstep : |u - v| / |v| ≤ (2 * ε) / (|a| / 2) :=
    div_le_div₀ (by linarith) h2ε (by linarith) hvabs
  have hfinal : (2 * ε) / (|a| / 2) = 4 * ε / |a| := by
    field_simp
    norm_num
  linarith

/-- The doubling ratio `y'/y` is `2^q` times the ratio of the two *normalised* values
`y'/(2t)^q`, `y/t^q`, with `(2t)^q = 2^q t^q`.  This is the identity that converts the two
`hPB`-asymptotics into the cluster condition. -/
private lemma ratio_rpow_eq (y y' t : ℝ) (ht : 0 < t) (q : ℚ) (hy : y ≠ 0) :
    |y' / y - (2:ℝ)^(q:ℝ)| =
      (2:ℝ)^(q:ℝ) * |(y' / (2*t)^(q:ℝ)) / (y / t^(q:ℝ)) - 1| := by
  have h2t : (2 * t) ^ (q:ℝ) = (2:ℝ) ^ (q:ℝ) * t ^ (q:ℝ) :=
    Real.mul_rpow (by norm_num) (le_of_lt ht)
  have hkey : y' / y = (2:ℝ)^(q:ℝ) * ((y' / (2*t)^(q:ℝ)) / (y / t^(q:ℝ))) := by
    rw [h2t]
    have h2q : (2:ℝ)^(q:ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
    have htq : t^(q:ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
    field_simp
  rw [hkey]
  have hfac : (2:ℝ)^(q:ℝ) * ((y' / (2 * t) ^ (q:ℝ)) / (y / t ^ (q:ℝ))) - (2:ℝ)^(q:ℝ) =
      (2:ℝ)^(q:ℝ) * ((y' / (2 * t) ^ (q:ℝ)) / (y / t ^ (q:ℝ)) - 1) := by ring
  rw [hfac, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) (q:ℝ))]

/-- The arithmetic core of the case `ρ = 2^q > 0`: a tolerance `ε ≤ |a| / (4 N ρ)` makes the
error `ρ · 4ε/|a|` smaller than `1/N`. -/
private lemma rpow_eps_bound (a eps rho : ℝ) (N : ℕ) (ha : 0 < |a|) (hrho : 0 < rho)
    (hN : 0 < N) (heps : eps ≤ |a| / (4 * (N:ℝ) * rho)) :
    rho * (4 * eps / |a|) ≤ 1 / (N:ℝ) := by
  have hN' : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have h1 : 4 * eps * rho ≤ |a| / (N:ℝ) := by
    have h2 : 4 * eps * rho ≤ 4 * (|a| / (4 * (N:ℝ) * rho)) * rho := by
      have h3 : eps * (4 * rho) ≤ (|a| / (4 * (N:ℝ) * rho)) * (4 * rho) :=
        mul_le_mul_of_nonneg_right heps (by positivity)
      nlinarith [h3]
    have h4 : 4 * (|a| / (4 * (N:ℝ) * rho)) * rho = |a| / (N:ℝ) := by
      field_simp
    linarith
  have h5 : rho * (4 * eps / |a|) = 4 * eps * rho / |a| := by ring
  rw [h5, div_le_iff₀ ha]
  have h6 : |a| / (N:ℝ) = 1 / (N:ℝ) * |a| := by ring
  linarith

theorem clusterE_pos {k : ℕ}
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hPB : WilkiesDesign.CG.PolyBoundedRExp)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y →
      Work.WilC4.Route.Gr Y c x y' → y = y')
    (B : Set (Fin (k + 1) → ℝ)) (N₀ : ℕ)
    (hBcard : ∀ c : Fin k → ℝ, {x : ℝ | Fin.cons x c ∈ B}.encard ≤ N₀)
    (hgf : Work.WilC4.GoodFibre Y B) :
    ∃ ρ ∈ Work.WilC4.Route.ClusterE Y B, 0 < ρ := by
  -- `Y` is `RExpExist` (area C0), so the polynomial-boundedness hypothesis `hPB` applies to it.
  have hYrex : WilkiesDesign.RExpExist Y := WilkiesDesign.CG.C0_rexp_syntax_proved hR Y hY
  obtain ⟨Qs, hQs⟩ := hPB k Y hYrex hfun
  let c : Fin k → ℝ := fun _ => 0
  -- the fibre of `B` at the parameter `c` is finite, hence has an upper bound
  have hBcfin : ({b : ℝ | Fin.cons b c ∈ B}).Finite :=
    Set.encard_lt_top_iff.mp (lt_of_le_of_lt (hBcard c) (ENat.natCast_lt_top N₀))
  obtain ⟨M, hM⟩ := hBcfin.bddAbove
  rcases hQs c with ⟨R0, hzero⟩ | ⟨q, -, a, ha, hasym⟩
  · -- the fibre is eventually `0`: impossible, since off the breakpoints it is nowhere zero
    exfalso
    set M' : ℝ := max M (max R0 0) + 1 with hM'def
    have hfree : ∀ x ∈ Set.Ioo M' (M' + 2), Fin.cons x c ∉ B := by
      intro x hx hxb
      have h1 : x ≤ M := hM hxb
      have h2 : M ≤ M' - 1 := by
        have h3 : M ≤ max M (max R0 0) := le_max_left _ _
        linarith
      linarith [hx.1]
    obtain ⟨hu, hne, -⟩ := hgf c M' (M' + 2) (by linarith) hfree
    have hxmem : M' + 1 ∈ Set.Ioo M' (M' + 2) := ⟨by linarith, by linarith⟩
    obtain ⟨y, hy, -⟩ := hu (M' + 1) hxmem
    have hy0 : y ≠ 0 := hne (M' + 1) hxmem y hy
    have hR0le : R0 ≤ M' + 1 := by
      have h3 : R0 ≤ max R0 0 := le_max_left _ _
      have h4 : max R0 0 ≤ max M (max R0 0) := le_max_right _ _
      linarith
    exact hy0 (hzero (M' + 1) y hR0le hy)
  · -- the fibre is asymptotic to `a x^q`: `ρ = 2^q > 0` is a cluster value
    set rho : ℝ := (2:ℝ) ^ (q:ℝ) with hrhodef
    have hrho_pos : 0 < rho := Real.rpow_pos_of_pos (by norm_num) _
    have haabs : 0 < |a| := abs_pos.mpr ha
    refine ⟨rho, ?_, hrho_pos⟩
    intro N hN
    have hN' : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    -- the tolerance that makes `2^q · 4ε/|a| ≤ 1/N`
    set eps : ℝ := min (|a| / 2) (|a| / (4 * (N:ℝ) * rho)) with hepsdef
    have heps_pos : 0 < eps := by
      rw [hepsdef]
      exact lt_min (by linarith) (by positivity)
    obtain ⟨R, hRasy⟩ := hasym eps heps_pos
    -- a positive point beyond the asymptotic threshold and beyond all breakpoints
    set X : ℝ := max (max 1 ((N:ℝ) * R)) (2 * (N:ℝ) * M) + 1 with hXdef
    have hXpos : 0 < X := by
      have h1 : (1:ℝ) ≤ max 1 ((N:ℝ) * R) := le_max_left _ _
      have h2 : max 1 ((N:ℝ) * R) ≤ max (max 1 ((N:ℝ) * R)) (2 * (N:ℝ) * M) :=
        le_max_left _ _
      linarith
    have hXR : R ≤ X / (N:ℝ) := by
      have h1 : (N:ℝ) * R ≤ max (max 1 ((N:ℝ) * R)) (2 * (N:ℝ) * M) :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      rw [le_div_iff₀ hN']
      nlinarith
    have hXdeep : M < X / (2 * (N:ℝ)) := by
      have h1 : 2 * (N:ℝ) * M ≤ max (max 1 ((N:ℝ) * R)) (2 * (N:ℝ) * M) :=
        le_max_right _ _
      rw [lt_div_iff₀ (by positivity)]
      nlinarith
    refine ⟨c, X, hXpos, ?_, ?_⟩
    · -- `X` is `N`-deep: every breakpoint of the fibre lies below `X/(2N)`
      intro b hb
      rintro ⟨h1, -⟩
      have hbM : b ≤ M := hM hb
      linarith
    · -- the ratio clause on the window `[X/N, XN]`
      intro t ht1 ht2 y y' hy hy' hy0
      have htpos : 0 < t := by
        have h1 : 0 < X / (N:ℝ) := div_pos hXpos hN'
        linarith
      have htR : R ≤ t := le_trans hXR ht1
      have h2tR : R ≤ 2 * t := by linarith
      have hu : |y / t ^ (q:ℝ) - a| < eps := hRasy t y htR hy
      have hv : |y' / (2 * t) ^ (q:ℝ) - a| < eps := hRasy (2 * t) y' h2tR hy'
      have hheps : eps ≤ |a| / 2 := by rw [hepsdef]; exact min_le_left _ _
      have hveq : y / t ^ (q:ℝ) ≠ 0 :=
        div_ne_zero hy0 (ne_of_gt (Real.rpow_pos_of_pos htpos _))
      have hstep : |(y' / (2 * t) ^ (q:ℝ)) / (y / t ^ (q:ℝ)) - 1| ≤ 4 * eps / |a| :=
        abs_div_sub_one_le hveq hv hu hheps
      have heps_bound : eps ≤ |a| / (4 * (N:ℝ) * rho) := by
        rw [hepsdef]; exact min_le_right _ _
      have hCN : rho * (4 * eps / |a|) ≤ 1 / (N:ℝ) :=
        rpow_eps_bound a eps rho N haabs hrho_pos hN heps_bound
      rw [ratio_rpow_eq y y' t htpos q hy0]
      calc rho * |(y' / (2 * t) ^ (q:ℝ)) / (y / t ^ (q:ℝ)) - 1|
          ≤ rho * (4 * eps / |a|) := mul_le_mul_of_nonneg_left hstep (le_of_lt hrho_pos)
        _ ≤ 1 / (N:ℝ) := hCN

end Work.WilC4
