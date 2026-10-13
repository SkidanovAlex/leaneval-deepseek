import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Taylor.taylor_conditions_of_holds
import Submission.Work.WilE3.Taylor.E3_residual_bound
import Submission.Work.WilE3.Taylor.E3_remainder_uniform
import Submission.Work.WilE3.Taylor.E3_infDist_le_of_pow_le
import Submission.Work.WilE3.Taylor.E3_lipschitz_eaTaylor
import Submission.Work.WilE3.Taylor.E3_pos_of_perturb_pointwise
import Submission.Work.WilE3.Taylor.E3_eqs_vanish_of_closure

namespace Work.WilE3.Taylor

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

/-! ## The two analytic inputs and the six auxiliary lemmas

The proof of `E3_taylor_closure_proved` below is assembled from

* `Work.WilE3.Taylor.E3_lipschitz_eaTaylor` — the Taylor polynomial is Lipschitz on a ball;
* `Work.WilE3.Taylor.E3_residual_bound` — the residual `∑ |f_i|` is `O (d^N)` on the Taylor set;
* `Work.WilE3.Taylor.E3_remainder_uniform` — the Taylor remainder `O (d^{κ+1})`, uniform over `B.pos`;
* `Work.WilE3.Taylor.E3_infDist_le_of_pow_le` — the Łojasiewicz exponent arithmetic `d^{κ²/q} ≪ d^κ`;
* `Work.WilE3.Taylor.E3_pos_of_perturb_pointwise` — moving by `o (d^κ)` keeps `g > 0`;
* `Work.WilE3.Taylor.E3_eqs_vanish_of_closure` — the zero set of the equations is non-empty;
* `Work.WilE3.Taylor.taylor_conditions_of_holds` — the equation half of the direction `⇒`.

-/

/-- **`E3_taylor_closure` (GV Cor. 4.5) from its two analytic inputs.**  The conclusion is the
frozen `WilkiesDesign.E.E3_taylor_closure`, verbatim.  The two leading hypotheses are the inputs of
Gabrielov 1998 (vision transcription `sources/wilkiesE/vision/gabrielov1998_frontier/p0007.md`–
`p0008.md`), neither of which is the conclusion:

* `hL` is the effective Łojasiewicz inequality for the *system residual* `∑_i |f_i|` against the
  *common* zero set `Z` of the system (Gabrielov 1995, Cor. 4.4; vocabulary `Work.WilE3.HasLoj`),
  with exponent `q > K.eval B.deg`.  (It must be the residual, not the individual equations: for
  `B.eqs = [X 0, X 0 - X 1]` the equation `X 0` vanishes along `{x₀ = 0}` while `Z = {0}`, so
  per-equation Łojasiewicz against `Z` is false.)  It drives the direction `⇐`: from the Taylor
  conditions (all `|f_i| ≤ d^{κ²}`, `d := dist x y`) the residual is `≤ I · d^{κ²}`, so
  `dist (x, Z) ≤ C d^{κ²/q}` with `κ²/q > κ`, and moving `x` to the nearest point of `Z` preserves
  `g_j > 0` because the Taylor polynomial dominates there while the remainder is `O (d^{κ+1})`.
* `hG` is Gabrielov's critical-set/maximal-`ψ` assertion (his Lemmas 2.3/2.4, proof of Lemma 2.5):
  every `y` in the closure of the basic set is the limit of points that satisfy the *equations* and
  the *Taylor* strict-inequality conditions of `taylorSet`.  It drives `⇒`.
* The equation half of `⇒` is proved in `Work.WilE3.Taylor.taylor_conditions_of_holds`;
  `API.eaTaylor_remainder` supplies the remainder bounds used in both directions.
* The exponent bookkeeping: pad `K` above `hL`'s and `hG`'s polynomials so that `K.eval B.deg < q`
  and `K.eval B.deg < κ` both hold. -/
theorem E3_taylor_closure_proved
    (hL : ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (B : Basic k r)
        (y : Fin k → ℝ) (q : ℕ), k + r ≤ F → K.eval B.deg < q →
        HasLoj (fun x => (B.eqs.map fun f => |eaEval c f x|).sum)
          {x | ∀ f' ∈ B.eqs, eaEval c f' x = 0} y q)
    (hG : ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (B : Basic k r)
        (y : Fin k → ℝ) (κ : ℕ), k + r ≤ F → K.eval B.deg < κ →
        y ∈ closure {x | B.holds c x} →
        y ∈ closure {x | (∀ f ∈ B.eqs, eaEval c f x = 0) ∧
          (∀ g ∈ B.pos, dist x y ^ κ < eaTaylor c g κ y x)}) :
    ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r)
    (B : Basic k r) (y : Fin k → ℝ) (κ : ℕ), k + r ≤ F → K.eval B.deg < κ →
    (y ∈ closure {x | B.holds c x} ↔
      y ∈ closure {x | (∀ f ∈ B.eqs, |eaTaylor c f (κ ^ 2) y x| ≤ dist x y ^ (κ ^ 2)) ∧
                       (∀ g ∈ B.pos, dist x y ^ κ < eaTaylor c g κ y x)}) := by
  intro F
  obtain ⟨K_L, hKL⟩ := hL F
  obtain ⟨K_G, hKG⟩ := hG F
  refine ⟨K_L + K_G + 2, ?_⟩
  intro k r c B y κ hkr hκ
  have hKev : (K_L + K_G + 2).eval B.deg = K_L.eval B.deg + K_G.eval B.deg + 2 := by simp
  have hκG : K_G.eval B.deg < κ := by omega
  have hκ1 : 1 ≤ κ := by omega
  set q : ℕ := K_L.eval B.deg + 1 with hqdef
  have hqL : K_L.eval B.deg < q := by rw [hqdef]; exact Nat.lt_succ_self _
  have hqpos : 0 < q := by rw [hqdef]; omega
  have hqκ : q + 1 ≤ κ := by rw [hqdef]; omega
  constructor
  · -- ==================== (⇒) ====================
    intro hcl
    have hGcl := hKG k r c B y κ hkr hκG hcl
    -- near `y`, the vanishing of the equations already gives the equation half of the Taylor set
    have hevTay : ∀ᶠ x in 𝓝 y, (∀ f ∈ B.eqs, eaEval c f x = 0) →
        ∀ f ∈ B.eqs, |eaTaylor c f (κ ^ 2) y x| ≤ dist x y ^ (κ ^ 2) := by
      filter_upwards [taylor_conditions_of_holds c ⟨B.eqs, []⟩ y κ] with x hx hxe f hf
      exact hx ⟨hxe, by simp⟩ f hf
    obtain ⟨ρ, hρpos, hρ⟩ := Metric.eventually_nhds_iff_ball.mp hevTay
    refine Metric.mem_closure_iff.mpr fun ε hε => ?_
    obtain ⟨x, hxA, hxd⟩ := Metric.mem_closure_iff.mp hGcl (min ρ ε) (lt_min hρpos hε)
    have hxρ : dist x y < ρ := by
      rw [dist_comm]; exact lt_of_lt_of_le hxd (min_le_left _ _)
    refine ⟨x, ⟨fun f hf => hρ x (Metric.mem_ball.mpr hxρ) hxA.1 f hf, hxA.2⟩, ?_⟩
    exact lt_of_lt_of_le hxd (min_le_right _ _)
  · -- ==================== (⇐) ====================
    intro hcl
    -- the equations vanish at `y`, so the common zero set `Z` of the system is non-empty
    have hyZ : ∀ f ∈ B.eqs, eaEval c f y = 0 := E3_eqs_vanish_of_closure c B y κ hκ1 hcl
    -- constants
    obtain ⟨I, hI0, R_I, hRIpos, hRes⟩ := E3_residual_bound c B y (κ ^ 2)
    obtain ⟨C_L, hCLpos, hLoj⟩ := hKL k r c B y q hkr hqL
    have hLipEx : ∀ g : EAPoly k r, ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : Fin k → ℝ,
        dist a y ≤ 1 → dist b y ≤ 1 →
          |eaTaylor c g κ y b - eaTaylor c g κ y a| ≤ C * dist b a :=
      fun g => E3_lipschitz_eaTaylor c g κ y 1 zero_le_one
    choose Lam hLam0 hLam using hLipEx
    obtain ⟨Crew, R_rem, hCrew0, hRrempos, hRemU⟩ := E3_remainder_uniform c B y κ
    set LamSum : ℝ := (B.pos.map Lam).sum with hLamSumdef
    have hAll0 : ∀ y ∈ (B.pos.map Lam), 0 ≤ y := by
      intro y hy
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hy
      exact hLam0 g
    have hLamSum0 : 0 ≤ LamSum := by
      rw [hLamSumdef]; exact List.sum_nonneg hAll0
    have hLamLe : ∀ g ∈ B.pos, Lam g ≤ LamSum := by
      intro g hg
      rw [hLamSumdef]
      exact List.single_le_sum (l := B.pos.map Lam) hAll0 (Lam g)
        (List.mem_map.mpr ⟨g, hg, rfl⟩)
    set C₂ : ℝ := max 1 (I / C_L) with hC₂def
    set C₃ : ℝ := C₂ + 1 with hC₃def
    set Δ : ℝ := max 1 (LamSum * C₃ + Crew * 2 ^ (κ + 1)) with hΔdef
    have hC₂1 : 1 ≤ C₂ := by rw [hC₂def]; exact le_max_left _ _
    have hC₃0 : 0 ≤ C₃ := by rw [hC₃def]; linarith
    have hC₃1 : 1 ≤ C₃ := by rw [hC₃def]; linarith
    have hΔ1 : 1 ≤ Δ := by rw [hΔdef]; exact le_max_left _ _
    have hΔpos : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ1
    -- the finitely many smallness conditions on `d = dist x y`, packaged as one eventual statement
    have hEv2 : ∀ᶠ x in 𝓝 y, dist x y < R_I := Metric.ball_mem_nhds y hRIpos
    have hEv3 : ∀ᶠ x in 𝓝 y, 2 * dist x y < R_rem := by
      filter_upwards [Metric.ball_mem_nhds y (show (0 : ℝ) < R_rem / 2 by linarith)] with x hx
      have h := Metric.mem_ball.mp hx
      linarith
    have hEv4 : ∀ᶠ x in 𝓝 y, dist x y ≤ 1 / 2 := by
      filter_upwards [Metric.ball_mem_nhds y (show (0 : ℝ) < 1 / 2 by norm_num)] with x hx
      exact le_of_lt (Metric.mem_ball.mp hx)
    have hEv5 : ∀ᶠ x in 𝓝 y, C₃ * dist x y ≤ 1 / 2 := by
      filter_upwards [Metric.ball_mem_nhds y (show (0 : ℝ) < 1 / (2 * C₃) by positivity)]
        with x hx
      have h := Metric.mem_ball.mp hx
      have hC₃pos : 0 < C₃ := lt_of_lt_of_le zero_lt_one hC₃1
      have h2 : C₃ * (1 / (2 * C₃)) = 1 / 2 := by field_simp
      have h3 : C₃ * dist x y < 1 / 2 := by
        rw [← h2]
        exact mul_lt_mul_of_pos_left h hC₃pos
      linarith
    have hEv6 : ∀ᶠ x in 𝓝 y, Δ * dist x y < 1 := by
      filter_upwards [Metric.ball_mem_nhds y (show (0 : ℝ) < 1 / Δ by positivity)] with x hx
      have h := Metric.mem_ball.mp hx
      have h2 : Δ * (1 / Δ) = 1 := by rw [mul_one_div, div_self (ne_of_gt hΔpos)]
      rw [← h2]
      exact mul_lt_mul_of_pos_left h hΔpos
    have hPkg : ∀ᶠ x in 𝓝 y,
        (C_L * Metric.infDist x {z : Fin k → ℝ | ∀ f ∈ B.eqs, eaEval c f z = 0} ^ q
          ≤ |(B.eqs.map fun f => |eaEval c f x|).sum|) ∧
        (dist x y < R_I) ∧ (2 * dist x y < R_rem) ∧ (dist x y ≤ 1 / 2) ∧
        (C₃ * dist x y ≤ 1 / 2) ∧ (Δ * dist x y < 1) := by
      filter_upwards [hLoj, hEv2, hEv3, hEv4, hEv5, hEv6] with x h1 h2 h3 h4 h5 h6
      exact ⟨h1, h2, h3, h4, h5, h6⟩
    refine Metric.mem_closure_iff.mpr fun ε hε => ?_
    obtain ⟨ρ, hρpos, hρ⟩ := Metric.eventually_nhds_iff_ball.mp hPkg
    obtain ⟨x, hxT, hxd⟩ :=
      Metric.mem_closure_iff.mp hcl (min ρ (ε / 2)) (lt_min hρpos (by linarith))
    have hdρ : dist x y < ρ := by
      rw [dist_comm]; exact lt_of_lt_of_le hxd (min_le_left _ _)
    have hdε : dist x y < ε / 2 := by
      rw [dist_comm]; exact lt_of_lt_of_le hxd (min_le_right _ _)
    obtain ⟨hŁoj, hdRI, hd2R, hd12, hdCd, hdΔ⟩ := hρ x (Metric.mem_ball.mpr hdρ)
    obtain ⟨hxTeq, hxTpos⟩ := hxT
    -- the residual bound and the Łojasiewicz inequality at `x`
    have hres := hRes x hdRI (fun f hf => hxTeq f hf)
    have hres0 : 0 ≤ (B.eqs.map fun f => |eaEval c f x|).sum :=
      List.sum_nonneg (fun y hy => by
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hy
        exact abs_nonneg _)
    have hŁoj' : C_L * Metric.infDist x {z : Fin k → ℝ | ∀ f ∈ B.eqs, eaEval c f z = 0} ^ q
        ≤ I * dist x y ^ (κ ^ 2) := by
      refine le_trans hŁoj ?_
      rw [abs_of_nonneg hres0]
      exact hres
    have hη : Metric.infDist x {z : Fin k → ℝ | ∀ f ∈ B.eqs, eaEval c f z = 0}
        ≤ C₂ * dist x y ^ (κ + 1) :=
      E3_infDist_le_of_pow_le _ x (I * dist x y ^ (κ ^ 2)) C_L I (dist x y) q κ hCLpos hI0
        dist_nonneg (le_trans hd12 (by norm_num)) hqpos hqκ hŁoj' le_rfl
    -- a point `z` of the zero set close to `x`
    have hZne : ({z : Fin k → ℝ | ∀ f ∈ B.eqs, eaEval c f z = 0} : Set (Fin k → ℝ)).Nonempty :=
      ⟨y, hyZ⟩
    obtain ⟨z, hzZ, hzx⟩ : ∃ z ∈ {z : Fin k → ℝ | ∀ f ∈ B.eqs, eaEval c f z = 0},
        dist x z ≤ C₃ * dist x y ^ (κ + 1) := by
      by_cases hd0 : dist x y = 0
      · have hxy : x = y := dist_eq_zero.mp hd0
        refine ⟨x, ?_, ?_⟩
        · rw [hxy]; exact hyZ
        · rw [hxy, dist_self, zero_pow (by omega : κ + 1 ≠ 0)]
          simp
      · have hdpos : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hd0)
        obtain ⟨z, hzZ, hzx'⟩ := Metric.infDist_lt_iff hZne |>.mp
          (lt_add_of_pos_right _ (pow_pos hdpos (κ + 1)))
        refine ⟨z, hzZ, le_trans (le_of_lt hzx') ?_⟩
        rw [hC₃def]
        nlinarith [hη]
    have hxy1 : dist x y ≤ 1 := by linarith
    -- `z` is within `2 d` of `y` (so that the Taylor remainder at `z` is available)
    have hCdκ : C₃ * dist x y ^ (κ + 1) ≤ (1 / 2) * dist x y := by
      have hdκ : dist x y ^ κ ≤ dist x y := by
        simpa using pow_le_pow_of_le_one (m := 1) (n := κ) dist_nonneg hxy1 hκ1
      have h1 : C₃ * dist x y ^ κ ≤ 1 / 2 :=
        le_trans (mul_le_mul_of_nonneg_left hdκ hC₃0) hdCd
      calc C₃ * dist x y ^ (κ + 1) = (C₃ * dist x y ^ κ) * dist x y := by
            rw [pow_succ]; ring
        _ ≤ (1 / 2) * dist x y := mul_le_mul_of_nonneg_right h1 dist_nonneg
    have hzy : dist z y ≤ 2 * dist x y := by
      have h1 : dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
      have h2 : dist z x ≤ (1 / 2) * dist x y := le_trans (by rw [dist_comm]; exact hzx) hCdκ
      linarith [dist_nonneg (x := x) (y := y)]
    have hzy1 : dist z y ≤ 1 := by linarith
    have hzR : dist z y < R_rem := lt_of_le_of_lt hzy hd2R
    -- the two pointwise estimates at `(z, x)`
    have hLipx : ∀ g ∈ B.pos,
        |eaTaylor c g κ y z - eaTaylor c g κ y x| ≤ LamSum * dist z x := by
      intro g hg
      exact le_trans (hLam g x z hxy1 hzy1)
        (mul_le_mul_of_nonneg_right (hLamLe g hg) dist_nonneg)
    have hRemz : ∀ g ∈ B.pos,
        |eaEval c g z - eaTaylor c g κ y z| ≤ Crew * dist z y ^ (κ + 1) :=
      fun g hg => hRemU g hg z hzR
    have hd3 : (LamSum * C₃ + Crew * 2 ^ (κ + 1)) * dist x y < 1 := by
      have hle : LamSum * C₃ + Crew * 2 ^ (κ + 1) ≤ Δ := by
        rw [hΔdef]; exact le_max_right _ _
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle dist_nonneg) hdΔ
    have hzpos : ∀ g ∈ B.pos, 0 < eaEval c g z :=
      E3_pos_of_perturb_pointwise c B y x z κ C₃ LamSum Crew hC₃0 hLamSum0 hCrew0 hκ1
        hxTpos hzx hzy hLipx hRemz hd3
    -- `z ∈ B.holds` and it is within `ε` of `y`
    refine ⟨z, ⟨fun f hf => hzZ f hf, hzpos⟩, ?_⟩
    have hzy2 : dist y z ≤ 2 * dist x y := by rw [dist_comm]; exact hzy
    linarith

end Work.WilE3.Taylor
