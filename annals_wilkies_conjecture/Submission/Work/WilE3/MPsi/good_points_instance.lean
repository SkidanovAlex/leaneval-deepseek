import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.MPsi.Defs
import Submission.Work.WilE3.MPsi.exists_zero_near
import Submission.Work.WilE3.MPsi.atomDeg_phiPen_le
import Submission.Work.WilE3.MPsi.ascent
import Submission.Work.WilE3.MPsi.lip_bound_list
import Submission.Work.WilE3.MPsi.final_arith
import Submission.Work.WilE3.MPsi.rpow_P_bound
import Submission.Work.WilE3.Taylor.MaximalPsi

namespace Work.WilE3.MPsi

open Classical Topology Filter
open WilkiesDesign.E

variable {k r : ℕ}

/-! ### Elementary evaluation and continuity lemmas -/

/-- The evaluation of the product `psiProd B` is the product of the evaluations. -/
lemma gpi_eaEval_psiProd (c : EAChain k r) (B : Basic k r) (x : Fin k → ℝ) :
    eaEval c (psiProd B) x = (B.pos.map (fun g => eaEval c g x)).prod := by
  unfold psiProd eaEval
  rw [map_list_prod]

/-- The evaluation of the sum of squares `resid B` is the sum of the squares of the evaluations. -/
lemma gpi_eaEval_resid (c : EAChain k r) (B : Basic k r) (x : Fin k → ℝ) :
    eaEval c (resid B) x = (B.eqs.map (fun f => eaEval c f x ^ 2)).sum := by
  unfold resid eaEval
  rw [map_list_sum]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro f _
  rw [Function.comp_apply, map_pow]

/-- The evaluation of the penalised product `phiPen B ν`. -/
lemma gpi_eaEval_phiPen (c : EAChain k r) (B : Basic k r) (ν : ℕ) (x : Fin k → ℝ) :
    eaEval c (phiPen B ν) x
      = eaEval c (psiProd B) x *
        (eaEval c (psiProd B) x ^ (2 * ν) - eaEval c (resid B) x) := by
  unfold phiPen eaEval
  rw [map_mul, map_sub, map_pow]

/-- `eaEval c Q` is `C¹`. -/
lemma gpi_contDiff (c : EAChain k r) (Q : EAPoly k r) :
    ContDiff ℝ 1 (fun x : Fin k → ℝ => eaEval c Q x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (eaEval_analytic c Q x).contDiffAt

/-- `eaEval c Q` is continuous. -/
lemma gpi_continuous (c : EAChain k r) (Q : EAPoly k r) :
    Continuous (fun x : Fin k → ℝ => eaEval c Q x) :=
  (gpi_contDiff c Q).continuous

/-! ### Product bounds for positive lists -/

/-- A product of numbers in `[0, C]` is bounded by `C ^ length`. -/
lemma gpi_list_prod_le_pow {l : List ℝ} {C : ℝ} (hl : ∀ x ∈ l, 0 ≤ x ∧ x ≤ C) :
    l.prod ≤ C ^ l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons, List.length_cons]
    have ha := hl a List.mem_cons_self
    have ht : ∀ x ∈ t, 0 ≤ x ∧ x ≤ C := fun x hx => hl x (List.mem_cons_of_mem a hx)
    have hpn : 0 ≤ t.prod := List.prod_nonneg (fun x hx => (ht x hx).1)
    calc a * t.prod ≤ C * C ^ t.length := mul_le_mul ha.2 (ih ht) hpn (le_trans ha.1 ha.2)
      _ = C ^ (t.length + 1) := by rw [pow_succ]; ring

/-- `X * (1 / (X + 1)) ≤ 1` for `X ≥ 0`. -/
lemma gpi_self_mul_inv_le_one {X : ℝ} (hX : 0 ≤ X) : X * (1 / (X + 1)) ≤ 1 := by
  rw [mul_one_div, div_le_iff₀ (by linarith : (0 : ℝ) < X + 1)]
  linarith

/-- `c * (a / (b * c)) = a / b`. -/
lemma gpi_mul_div_mul {a b c : ℝ} (hb : b ≠ 0) (hc : c ≠ 0) : c * (a / (b * c)) = a / b := by
  field_simp

/-- If `a ∈ l` and all elements of `l` lie in `[0, C]` with `C ≥ 1`, then
`l.prod ≤ a * C ^ l.length`. -/
lemma gpi_list_prod_le_mul_length {l : List ℝ} {a C : ℝ} (ha : a ∈ l) (hC : 1 ≤ C)
    (hl : ∀ x ∈ l, 0 ≤ x ∧ x ≤ C) : l.prod ≤ a * C ^ l.length := by
  classical
  rw [← List.prod_erase ha]
  refine mul_le_mul_of_nonneg_left ?_ (hl a ha).1
  calc (l.erase a).prod ≤ C ^ (l.erase a).length :=
        gpi_list_prod_le_pow (fun x hx => hl x (List.mem_of_mem_erase hx))
    _ ≤ C ^ l.length := pow_le_pow_right₀ hC (List.length_erase_le)

/-! ### The basic EA set and its closure -/

/-- Every equation of `B` vanishes at a limit point of `B.holds`. -/
lemma gpi_eqs_zero_of_mem_closure (c : EAChain k r) (B : Basic k r) {y : Fin k → ℝ}
    (hy : y ∈ closure {x | B.holds c x}) : ∀ f ∈ B.eqs, eaEval c f y = 0 := by
  intro f hf
  have hclosed : IsClosed {x : Fin k → ℝ | eaEval c f x = 0} :=
    isClosed_eq (gpi_continuous c f) continuous_const
  exact (closure_minimal (fun x hx => hx.1 f hf) hclosed) hy

/-- Every strict inequality of `B` is nonnegative at a limit point of `B.holds`. -/
lemma gpi_pos_nonneg_of_mem_closure (c : EAChain k r) (B : Basic k r) {y : Fin k → ℝ}
    (hy : y ∈ closure {x | B.holds c x}) : ∀ g ∈ B.pos, 0 ≤ eaEval c g y := by
  intro g hg
  have hclosed : IsClosed {x : Fin k → ℝ | 0 ≤ eaEval c g x} :=
    isClosed_le continuous_const (gpi_continuous c g)
  exact (closure_minimal (fun x hx => le_of_lt (hx.2 g hg)) hclosed) hy

/-- The set `{x | ∀ g ∈ l, 0 ≤ eaEval c g x}` is closed. -/
lemma gpi_isClosed_nonneg (c : EAChain k r) (l : List (EAPoly k r)) :
    IsClosed {x : Fin k → ℝ | ∀ g ∈ l, 0 ≤ eaEval c g x} := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have heq : {x : Fin k → ℝ | ∀ g ∈ a :: t, 0 ≤ eaEval c g x}
        = {x : Fin k → ℝ | 0 ≤ eaEval c a x} ∩
          {x : Fin k → ℝ | ∀ g ∈ t, 0 ≤ eaEval c g x} := by
      ext x; constructor
      · intro h; exact ⟨h a List.mem_cons_self, fun g hg => h g (List.mem_cons_of_mem a hg)⟩
      · rintro ⟨ha, ht⟩ g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact ha
        · exact ht g hg
    rw [heq]
    exact (isClosed_le continuous_const (gpi_continuous c a)).inter ih

/-- If all values `eaEval c g x` (`g ∈ l`) are positive then so are all values nearby. -/
lemma gpi_forall_mem_eventually (c : EAChain k r) (l : List (EAPoly k r)) {x : Fin k → ℝ}
    (h : ∀ g ∈ l, 0 < eaEval c g x) :
    ∀ᶠ x' in 𝓝 x, ∀ g ∈ l, 0 < eaEval c g x' := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : ∀ᶠ x' in 𝓝 x, 0 < eaEval c a x' :=
      (isOpen_lt continuous_const (gpi_continuous c a)).mem_nhds (h a List.mem_cons_self)
    have ht : ∀ᶠ x' in 𝓝 x, ∀ g ∈ t, 0 < eaEval c g x' :=
      ih (fun g hg => h g (List.mem_cons_of_mem a hg))
    filter_upwards [ha, ht] with x' hx' hx't g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hx'
    · exact hx't g hg

/-- **The analytic core (one instance)**, namespace `Work.WilE3.MPsi`.  With the effective gradient
inequality for the EA polynomial `Φ = phiPen B (2q)` at `y` (exponent `θ < 1`, `1/(1-θ) ≤ Kexp`) and
the residual Łojasiewicz inequality of exponent `q` for `B.eqs` at `y`, every `κ > Kexp` admits
points `z → y` lying *exactly* on `{f = 0}` with `g z > 2 · dist z y ^ κ`.

Proof (design `sources/wilkiesE3mpsi/wilkies_e3_maximalpsi.md`): trivial if `y ∈ B.holds`.  Else some
`g_{j₀} y = 0`.  Pick `x₀ ∈ B.holds` within `ρ` of `y` (so `Φ(x₀) = P^{4q+1} > 0`); apply the ascent
lemma `Work.WilE3.MPsi.ascent` (same directory) to `Φ` on `G = {g ≥ 0} ∩ {P^{4q} ≥ S}` (closed, and a
neighbourhood of each point where `Φ > 0`) to get `z ∈ G` within `2ρ` with `Φ z ≥ (cρ)^Kexp`; then
every `g z ≥ m := min g z ≳ (cρ)^Kexp` while `∑|f z| ≤ L·S^{1/2} ≲ m^{2q}`;
`Work.WilE3.MPsi.exists_zero_near` moves `z` to `z'` on `{f = 0}` with `dist z' z ≲ m²`, and the local
Lipschitz bound of `g` keeps `g z' ≥ m/2`.  The final exponent split is: if `A m² ≤ 2ρ` then
`2 (4ρ)^κ < c ρ^{Kexp}/2` for `κ ≥ Kexp+1`, else `2 (2 A m²)^κ < m/2`.
(If `Work.WilE3.MPsi.ascent` is not yet importable when you start, prove that estimate internally.) -/
theorem good_points_instance {k r : ℕ} (c : EAChain k r) (B : Basic k r) (y : Fin k → ℝ) (q : ℕ)
    (hq : 0 < q)
    (hL : Work.WilE3.HasLoj (fun x => (B.eqs.map fun f => |eaEval c f x|).sum)
      {x | ∀ f ∈ B.eqs, eaEval c f x = 0} y q)
    {θ cst : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hcst : 0 < cst)
    (hgr : ∀ᶠ x in 𝓝 y, cst * |eaEval c (Work.WilE3.MPsi.phiPen B (2 * q)) x| ^ θ ≤
      ‖fderiv ℝ (fun z => eaEval c (Work.WilE3.MPsi.phiPen B (2 * q)) z) x‖)
    (Kexp : ℕ) (hKexp : 1 / (1 - θ) ≤ (Kexp : ℝ))
    (hy : y ∈ closure {x | B.holds c x}) (κ : ℕ) (hκ : Kexp < κ) :
    ∀ ε : ℝ, 0 < ε → ∃ z : Fin k → ℝ, dist z y < ε ∧
      (∀ f ∈ B.eqs, eaEval c f z = 0) ∧ (∀ g ∈ B.pos, 2 * dist z y ^ κ < eaEval c g z) := by
  classical
  intro ε hε
  by_cases hholds : B.holds c y
  · refine ⟨y, by simpa using hε, fun f hf => hholds.1 f hf, fun g hg => ?_⟩
    rw [dist_self, zero_pow (by omega : κ ≠ 0)]
    simpa using hholds.2 g hg
  · -- Main case: `y ∉ B.holds`, so some strict inequality vanishes at `y`.
    have heqs_y : ∀ f ∈ B.eqs, eaEval c f y = 0 := gpi_eqs_zero_of_mem_closure c B hy
    have hpos_y : ∀ g ∈ B.pos, 0 ≤ eaEval c g y := gpi_pos_nonneg_of_mem_closure c B hy
    obtain ⟨g0, hg0mem, hg0val⟩ : ∃ g ∈ B.pos, eaEval c g y = 0 := by
      by_contra hcon
      simp only [not_exists, not_and] at hcon
      exact hholds ⟨heqs_y, fun g hg => lt_of_le_of_ne (hpos_y g hg) (Ne.symm (hcon g hg))⟩
    -- The input data: local Lipschitz bounds, projection constants, gradient inequality radius.
    obtain ⟨R, Cb, Lip, hRpos, hCb1, hLip0, hCbbd, hLipbd⟩ := lip_bound_list c B.pos y
    obtain ⟨C₀, δ, hC₀pos, hδpos, hEZN⟩ := exists_zero_near c B.eqs y q hq hL heqs_y
    obtain ⟨r_gr, hr_gr_pos, hr_gr⟩ := Metric.eventually_nhds_iff.mp hgr
    have hCbpos : 0 < Cb := lt_of_lt_of_le one_pos hCb1
    have hθ1' : 0 < 1 - θ := by linarith
    have hKexp_pos : 0 < (Kexp : ℝ) := by
      have h : 0 < (1 : ℝ) / (1 - θ) := div_pos one_pos hθ1'
      linarith
    have hKexp1 : 1 ≤ Kexp := by
      have h2 : (0 : ℕ) < Kexp := by exact_mod_cast hKexp_pos
      omega
    have hκ' : Kexp + 1 ≤ κ := hκ
    have hqne : q ≠ 0 := by omega
    -- The constants of the estimate.
    set L : ℕ := B.pos.length with hLdef
    have hCbLpos : 0 < Cb ^ L := pow_pos hCbpos L
    set A : ℝ := (1 - θ) * cst / (4 * (k + 1)) with hAdef
    have hApos : 0 < A := by rw [hAdef]; positivity
    set s : ℝ := 1 / (1 - θ) with hsdef
    have hs_pos : 0 < s := by rw [hsdef]; exact div_pos one_pos hθ1'
    have hs_le : s ≤ (Kexp : ℝ) := by rw [hsdef]; exact hKexp
    set c₁ : ℝ := A ^ (s / (4 * q + 1)) / Cb ^ L with hc₁def
    have hc₁pos : 0 < c₁ := by
      rw [hc₁def]
      exact div_pos (Real.rpow_pos_of_pos hApos _) hCbLpos
    set K₀ : ℝ := ((B.eqs.length : ℝ) + 1) * Cb ^ (2 * q * L) with hK₀def
    have hK₀pos : 0 < K₀ := by rw [hK₀def]; positivity
    set A' : ℝ := (C₀ * K₀) ^ (1 / (q : ℝ)) with hA'def
    have hA'pos : 0 < A' := by
      rw [hA'def]
      exact Real.rpow_pos_of_pos (mul_pos hC₀pos hK₀pos) _
    -- Choose a small radius `ρ` satisfying all the constraints of the estimate.
    obtain ⟨ρ, hρpos, hρ1, hρε, hρδ, hρR, hρgr, hρc, hρA, hρL⟩ :
        ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ρ ≤ ε / 8 ∧ ρ ≤ δ / 8 ∧ ρ ≤ R / 8 ∧ ρ ≤ r_gr / 8 ∧
          ρ ≤ c₁ / (2 * 4 ^ (κ + 1)) ∧ ρ ≤ 1 / (4 * A' * Lip ^ 2 + 1) ∧
          ρ ≤ 1 / (8 * Lip ^ 2 * A' + 1) := by
      refine ⟨min (ε / 8) (min (δ / 8) (min (R / 8) (min (r_gr / 8)
        (min 1 (min (c₁ / (2 * 4 ^ (κ + 1))) (min (1 / (4 * A' * Lip ^ 2 + 1))
          (1 / (8 * Lip ^ 2 * A' + 1)))))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · positivity
      · simp [min_le_iff]
      · simp [min_le_iff]
      · simp [min_le_iff]
      · simp [min_le_iff]
      · simp [min_le_iff]
      · simp [min_le_iff]
      · simp [min_le_iff]
      · simp [min_le_iff]
    -- A point of `B.holds` within `ρ` of `y`.
    obtain ⟨x0, hx0holds, hx0dist⟩ : ∃ x0 : Fin k → ℝ, B.holds c x0 ∧ dist x0 y < ρ := by
      obtain ⟨x0, hx0m, hx0d⟩ := Metric.mem_closure_iff.mp hy ρ hρpos
      exact ⟨x0, hx0m, by rwa [dist_comm] at hx0d⟩
    -- The closed set `G = {g ≥ 0} ∩ {P^{4q} ≥ S}`.
    set G : Set (Fin k → ℝ) :=
      {x | (∀ g ∈ B.pos, 0 ≤ eaEval c g x) ∧
        eaEval c (resid B) x ≤ eaEval c (psiProd B) x ^ (4 * q)} with hGdef
    have hGclosed : IsClosed G := by
      have hclosed1 : IsClosed {x : Fin k → ℝ | ∀ g ∈ B.pos, 0 ≤ eaEval c g x} :=
        gpi_isClosed_nonneg c B.pos
      have hclosed2 : IsClosed {x : Fin k → ℝ |
          eaEval c (resid B) x ≤ eaEval c (psiProd B) x ^ (4 * q)} :=
        isClosed_le (gpi_continuous c (resid B)) ((gpi_continuous c (psiProd B)).pow (4 * q))
      rw [hGdef]
      exact hclosed1.inter hclosed2
    -- `G` is a neighbourhood of every point where `Φ > 0`.
    have hGo : ∀ x ∈ G, 0 < eaEval c (phiPen B (2 * q)) x → G ∈ 𝓝 x := by
      intro x hxG hxΦ
      rw [hGdef] at hxG ⊢
      have h2q : 2 * (2 * q) = 4 * q := by ring
      rw [gpi_eaEval_phiPen, h2q] at hxΦ
      have hPx_nonneg : 0 ≤ eaEval c (psiProd B) x := by
        rw [gpi_eaEval_psiProd]
        exact List.prod_nonneg (fun z hz => by
          obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hz
          exact hxG.1 g hg)
      have hPx_pos : 0 < eaEval c (psiProd B) x := by
        rcases mul_pos_iff.mp hxΦ with ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h (not_lt.mpr hPx_nonneg)
      have hSx_lt : eaEval c (resid B) x < eaEval c (psiProd B) x ^ (4 * q) := by
        rcases mul_pos_iff.mp hxΦ with ⟨_, h⟩ | ⟨h, _⟩
        · linarith
        · exact absurd h (not_lt.mpr hPx_nonneg)
      have hfac : ∀ g ∈ B.pos, 0 < eaEval c g x := by
        intro g hg
        rcases lt_or_eq_of_le (hxG.1 g hg) with h | h
        · exact h
        · exfalso
          have hmem : eaEval c g x ∈ B.pos.map (fun g => eaEval c g x) :=
            List.mem_map_of_mem (f := fun g => eaEval c g x) hg
          have hzero : (B.pos.map (fun g => eaEval c g x)).prod = 0 :=
            List.prod_eq_zero_iff.mpr (by rw [← h] at hmem; exact hmem)
          rw [← gpi_eaEval_psiProd] at hzero
          exact absurd hzero (ne_of_gt hPx_pos)
      have hev1 : ∀ᶠ x' in 𝓝 x, ∀ g ∈ B.pos, 0 ≤ eaEval c g x' := by
        filter_upwards [gpi_forall_mem_eventually c B.pos hfac] with x' hx'
        exact fun g hg => le_of_lt (hx' g hg)
      have hev2 : ∀ᶠ x' in 𝓝 x,
          eaEval c (resid B) x' ≤ eaEval c (psiProd B) x' ^ (4 * q) := by
        have hopen : IsOpen {x' : Fin k → ℝ |
            eaEval c (resid B) x' < eaEval c (psiProd B) x' ^ (4 * q)} :=
          isOpen_lt (gpi_continuous c (resid B)) ((gpi_continuous c (psiProd B)).pow (4 * q))
        filter_upwards [hopen.mem_nhds hSx_lt] with x' hx'
        exact le_of_lt hx'
      filter_upwards [hev1, hev2] with x' h1 h2
      exact ⟨h1, h2⟩
    -- The gradient inequality holds on `G ∩ closedBall x0 ρ`.
    have hgr_G : ∀ x ∈ G, dist x x0 ≤ ρ → 0 < eaEval c (phiPen B (2 * q)) x →
        cst * eaEval c (phiPen B (2 * q)) x ^ θ ≤
          ‖fderiv ℝ (fun z : Fin k → ℝ => eaEval c (phiPen B (2 * q)) z) x‖ := by
      intro x hxG hdx hxΦ
      have hdy : dist x y < r_gr := by
        have h1 : dist x y ≤ dist x x0 + dist x0 y := dist_triangle x x0 y
        linarith
      have h := hr_gr (y := x) hdy
      rwa [abs_of_pos hxΦ] at h
    -- `x0 ∈ G` and `Φ x0 > 0`.
    have hPx0_pos : 0 < eaEval c (psiProd B) x0 := by
      rw [gpi_eaEval_psiProd]
      refine List.prod_pos (fun z hz => ?_)
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hz
      exact hx0holds.2 g hg
    have hSx0 : eaEval c (resid B) x0 = 0 := by
      rw [gpi_eaEval_resid]
      refine List.sum_eq_zero (fun z hz => ?_)
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hz
      rw [hx0holds.1 f hf, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    have hx0G : x0 ∈ G := by
      rw [hGdef]
      exact ⟨fun g hg => le_of_lt (hx0holds.2 g hg),
        by rw [hSx0]; exact pow_nonneg (le_of_lt hPx0_pos) _⟩
    have hΦx0 : 0 < eaEval c (phiPen B (2 * q)) x0 := by
      have h2q : 2 * (2 * q) = 4 * q := by ring
      rw [gpi_eaEval_phiPen, h2q, hSx0, sub_zero]
      exact mul_pos hPx0_pos (pow_pos hPx0_pos _)
    -- Ascent.
    obtain ⟨z, hzG, hzρ, hzΦ⟩ := ascent (fun x : Fin k → ℝ => eaEval c (phiPen B (2 * q)) x)
      (gpi_contDiff c (phiPen B (2 * q))) G hGclosed hGo hρpos hθ0 hθ1 hcst hgr_G hx0G hΦx0
    have hzy_le : dist z y ≤ 2 * ρ := by
      have h1 : dist z y ≤ dist z x0 + dist x0 y := dist_triangle z x0 y
      linarith
    have hzy_lt : dist z y < δ := by linarith
    have hzR : dist z y ≤ R := by linarith
    have hzG' : (∀ g ∈ B.pos, 0 ≤ eaEval c g z) ∧
        eaEval c (resid B) z ≤ eaEval c (psiProd B) z ^ (4 * q) := by
      have h := hzG
      rw [hGdef] at h
      exact h
    -- Lower bounds at `z`.
    have hbase : (A * ρ) ^ s ≤ eaEval c (phiPen B (2 * q)) z := by
      have h1 : A * ρ = (1 - θ) * cst * ρ / (4 * (k + 1)) := by rw [hAdef]; ring
      have h2 : s = 1 / (1 - θ) := hsdef
      rw [h1, h2]
      exact hzΦ
    have hΦz_pos : 0 < eaEval c (phiPen B (2 * q)) z :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (mul_pos hApos hρpos) s) hbase
    have hPz_nonneg : 0 ≤ eaEval c (psiProd B) z := by
      rw [gpi_eaEval_psiProd]
      exact List.prod_nonneg (fun y' hy' => by
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hy'
        exact hzG'.1 g hg)
    have hSz_nonneg : 0 ≤ eaEval c (resid B) z := by
      rw [gpi_eaEval_resid]
      exact List.sum_nonneg (fun y' hy' => by
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hy'
        positivity)
    have hΦz_le : eaEval c (phiPen B (2 * q)) z ≤ eaEval c (psiProd B) z ^ (4 * q + 1) := by
      have h2q : 2 * (2 * q) = 4 * q := by ring
      rw [gpi_eaEval_phiPen, h2q]
      calc eaEval c (psiProd B) z *
            (eaEval c (psiProd B) z ^ (4 * q) - eaEval c (resid B) z)
          ≤ eaEval c (psiProd B) z * eaEval c (psiProd B) z ^ (4 * q) :=
            mul_le_mul_of_nonneg_left (by linarith) hPz_nonneg
        _ = eaEval c (psiProd B) z ^ (4 * q + 1) := by rw [pow_succ]; ring
    have hP_low : A ^ (s / (4 * q + 1)) * ρ ^ Kexp ≤ eaEval c (psiProd B) z :=
      rpow_P_bound hApos hρpos hρ1 hPz_nonneg (le_of_lt hΦz_pos) hs_le hs_pos hbase hΦz_le
    -- The uniform lower bound `m` for all the strict inequalities at `z`.
    set m : ℝ := eaEval c (psiProd B) z / Cb ^ L with hmdef
    have hm_low : c₁ * ρ ^ Kexp ≤ m := by
      rw [hmdef, hc₁def, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hP_low hCbLpos.le
    have hm_pos : 0 < m := lt_of_lt_of_le (mul_pos hc₁pos (pow_pos hρpos Kexp)) hm_low
    have hmg : ∀ g ∈ B.pos, m ≤ eaEval c g z := by
      intro g hg
      have hbounded : ∀ y' ∈ B.pos.map (fun g => eaEval c g z), 0 ≤ y' ∧ y' ≤ Cb := by
        intro y' hy'
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hy'
        exact ⟨hzG'.1 g' hg', le_trans (le_abs_self _) (hCbbd g' hg' z hzR)⟩
      have hprod := gpi_list_prod_le_mul_length (l := B.pos.map (fun g => eaEval c g z))
        (a := eaEval c g z) (C := Cb)
        (List.mem_map_of_mem (f := fun g => eaEval c g z) hg) hCb1 hbounded
      rw [List.length_map, ← hLdef] at hprod
      rw [hmdef, gpi_eaEval_psiProd]
      exact (div_le_iff₀ hCbLpos).mpr hprod
    have hm_g0 : m ≤ eaEval c g0 z := hmg g0 hg0mem
    have hm_upper : m ≤ 2 * Lip * ρ := by
      have hbd := hLipbd g0 hg0mem z y hzR (by simpa using hRpos.le)
      rw [hg0val, sub_zero] at hbd
      have h1 : eaEval c g0 z ≤ Lip * dist z y := le_trans (le_abs_self _) hbd
      have h2 : Lip * dist z y ≤ Lip * (2 * ρ) := mul_le_mul_of_nonneg_left hzy_le hLip0
      linarith
    -- The residual is bounded by a power of `m`.
    have hP_eq : eaEval c (psiProd B) z = Cb ^ L * m := by
      rw [hmdef, mul_div_cancel₀ _ (ne_of_gt hCbLpos)]
    have hS_le : eaEval c (resid B) z ≤ (Cb ^ L * m) ^ (4 * q) := by
      have h := hzG'.2
      rwa [hP_eq] at h
    have hsqrtS : Real.sqrt (eaEval c (resid B) z) ≤ (Cb ^ L * m) ^ (2 * q) := by
      have h0 : 0 ≤ Cb ^ L * m := mul_nonneg hCbLpos.le hm_pos.le
      calc Real.sqrt (eaEval c (resid B) z) ≤ Real.sqrt ((Cb ^ L * m) ^ (4 * q)) :=
            Real.sqrt_le_sqrt hS_le
        _ = (Cb ^ L * m) ^ (2 * q) := by
            rw [show 4 * q = (2 * q) * 2 from by ring, pow_mul,
              Real.sqrt_sq (pow_nonneg h0 _)]
    have hterm : ∀ f ∈ B.eqs, |eaEval c f z| ≤ Real.sqrt (eaEval c (resid B) z) := by
      intro f hf
      have h1 : eaEval c f z ^ 2 ≤ eaEval c (resid B) z := by
        rw [gpi_eaEval_resid]
        exact List.single_le_sum (fun y' hy' => by
            obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hy'
            positivity) _ (List.mem_map_of_mem (f := fun f => eaEval c f z ^ 2) hf)
      calc |eaEval c f z| = Real.sqrt (eaEval c f z ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (eaEval c (resid B) z) := Real.sqrt_le_sqrt h1
    have hsum_bound : (B.eqs.map (fun f => |eaEval c f z|)).sum ≤ K₀ * m ^ (2 * q) := by
      have h1 : (B.eqs.map (fun f => |eaEval c f z|)).sum
          ≤ (B.eqs.map (fun _ : EAPoly k r => Real.sqrt (eaEval c (resid B) z))).sum :=
        List.sum_le_sum (fun f hf => hterm f hf)
      have h2 : (B.eqs.map (fun _ : EAPoly k r => Real.sqrt (eaEval c (resid B) z))).sum
          = (B.eqs.length : ℝ) * Real.sqrt (eaEval c (resid B) z) := by
        induction B.eqs with
        | nil => simp
        | cons a t ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          rw [ih]
          push_cast
          ring
      have h4 : Real.sqrt (eaEval c (resid B) z)
          ≤ Cb ^ (2 * q * L) * m ^ (2 * q) := by
        calc Real.sqrt (eaEval c (resid B) z) ≤ (Cb ^ L * m) ^ (2 * q) := hsqrtS
          _ = Cb ^ (2 * q * L) * m ^ (2 * q) := by
              rw [mul_pow, ← pow_mul, show L * (2 * q) = 2 * q * L from by ring]
      have h5 : (B.eqs.length : ℝ) * Real.sqrt (eaEval c (resid B) z)
          ≤ ((B.eqs.length : ℝ) + 1) * (Cb ^ (2 * q * L) * m ^ (2 * q)) := by
        have hX : 0 ≤ Cb ^ (2 * q * L) * m ^ (2 * q) := by positivity
        have h6 : (B.eqs.length : ℝ) * Real.sqrt (eaEval c (resid B) z)
            ≤ (B.eqs.length : ℝ) * (Cb ^ (2 * q * L) * m ^ (2 * q)) :=
          mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg _)
        have h7 : (B.eqs.length : ℝ) * (Cb ^ (2 * q * L) * m ^ (2 * q))
            ≤ ((B.eqs.length : ℝ) + 1) * (Cb ^ (2 * q * L) * m ^ (2 * q)) :=
          mul_le_mul_of_nonneg_right (by linarith) hX
        linarith
      have h8 : ((B.eqs.length : ℝ) + 1) * (Cb ^ (2 * q * L) * m ^ (2 * q))
          = K₀ * m ^ (2 * q) := by
        rw [hK₀def]; ring
      linarith
    -- Project onto the zero set of the equations.
    obtain ⟨z', hz'Z, hz'dist⟩ := hEZN z hzy_lt
    have hA'q : A' ^ q = C₀ * K₀ := by
      rw [hA'def, ← Real.rpow_natCast]
      rw [← Real.rpow_mul (le_of_lt (mul_pos hC₀pos hK₀pos))]
      have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hqne
      rw [div_mul_cancel₀ 1 hqR, Real.rpow_one]
    have hz'_bound : dist z' z ^ q ≤ (A' * m ^ 2) ^ q := by
      have h1 : C₀ * (B.eqs.map fun f => |eaEval c f z|).sum ≤ C₀ * (K₀ * m ^ (2 * q)) :=
        mul_le_mul_of_nonneg_left hsum_bound hC₀pos.le
      have h2 : C₀ * (K₀ * m ^ (2 * q)) = (A' * m ^ 2) ^ q := by
        rw [mul_pow, hA'q, ← pow_mul]
        ring
      linarith
    have hz'z : dist z' z ≤ A' * m ^ 2 :=
      (pow_le_pow_iff_left₀ dist_nonneg (by positivity) hqne).mp hz'_bound
    -- The exponent bookkeeping.
    have h4pos : (0 : ℝ) < 4 ^ (κ + 1) := by positivity
    have h1 : 4 ^ (κ + 1) * ρ < c₁ := by
      have h := mul_le_mul_of_nonneg_left hρc h4pos.le
      have h2 : 4 ^ (κ + 1) * (c₁ / (2 * 4 ^ (κ + 1))) = c₁ / 2 := by
        rw [gpi_mul_div_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt h4pos)]
      linarith
    have hfin2 : 4 * A' * Lip ^ 2 * ρ ≤ 2 := by
      have hX : 0 ≤ 4 * A' * Lip ^ 2 := by positivity
      have h := gpi_self_mul_inv_le_one hX
      have h' : 4 * A' * Lip ^ 2 * ρ ≤ 1 :=
        le_trans (mul_le_mul_of_nonneg_left hρA hX) h
      linarith
    have hfin3 : 8 * Lip ^ 2 * A' * ρ ≤ 1 := by
      have hX : 0 ≤ 8 * Lip ^ 2 * A' := by positivity
      have h := gpi_self_mul_inv_le_one hX
      exact le_trans (mul_le_mul_of_nonneg_left hρL hX) h
    obtain ⟨hfin_a, hfin_b, hfin_c⟩ :=
      final_arith hρpos hρ1 hκ' hm_low hm_upper hc₁pos hLip0 hA'pos h1 hfin2 hfin3
    have hz'R : dist z' y ≤ R := by
      have h1 : dist z' y ≤ dist z' z + dist z y := dist_triangle z' z y
      linarith
    refine ⟨z', ?_, hz'Z, ?_⟩
    · have h1 : dist z' y ≤ A' * m ^ 2 + 2 * ρ := by
        have h2 : dist z' y ≤ dist z' z + dist z y := dist_triangle z' z y
        linarith
      have h3 : 4 * ρ < ε := by linarith
      linarith
    · intro g hg
      have hz'g : m / 2 ≤ eaEval c g z' := by
        have hbd := hLipbd g hg z' z hz'R hzR
        have h1 : |eaEval c g z' - eaEval c g z| ≤ Lip * (A' * m ^ 2) :=
          le_trans hbd (mul_le_mul_of_nonneg_left hz'z hLip0)
        have h2 : eaEval c g z' ≥ eaEval c g z - Lip * (A' * m ^ 2) := by
          have := (abs_le.mp h1).1
          linarith
        have h3 : Lip * (A' * m ^ 2) ≤ m / 2 := by
          have h4 : Lip * (A' * m ^ 2) = (Lip * A' * m) * m := by ring
          rw [h4]
          have h5 : (Lip * A' * m) * m ≤ (1 / 2) * m :=
            mul_le_mul_of_nonneg_right hfin_a hm_pos.le
          linarith
        linarith [hmg g hg]
      have hdist : dist z' y ^ κ ≤ (A' * m ^ 2 + 2 * ρ) ^ κ := by
        have h1 : dist z' y ≤ A' * m ^ 2 + 2 * ρ := by
          have h2 : dist z' y ≤ dist z' z + dist z y := dist_triangle z' z y
          linarith
        exact pow_le_pow_left₀ dist_nonneg h1 κ
      have hmain : 2 * dist z' y ^ κ < m / 2 := by
        have h1 : 2 * dist z' y ^ κ ≤ 2 * (A' * m ^ 2 + 2 * ρ) ^ κ :=
          mul_le_mul_of_nonneg_left hdist (by norm_num)
        linarith
      linarith

end Work.WilE3.MPsi
