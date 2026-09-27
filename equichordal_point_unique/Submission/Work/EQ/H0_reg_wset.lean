import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.exists_regular_of_family
import Submission.Work.EQ.chain_eq_candChain_of_tails
import Submission.Work.EQ.fan_estimates
import Submission.Work.EQ.H0_countable_fibre
import Submission.Work.EQ.countable_regular_values
import Submission.Work.EQ.charVal_set
import Submission.Work.EQ.eqRelC_candChain

/-!
# Step 5 of `Work.EQ.H0_regular`: the `W`-sets and branch counting

This file carries the "branch counting" half of Rychlik's Theorem 11 (the design's step 5):
the explicit candidate chain `candChain a h ε η s N C z` has `ψ₁ = z` and `ψ₂ = C/z`, hence
invariant parameter `ψ ≡ C`; an analytic family of such chains therefore produces a *regular*
component of value `C`.
-/

namespace Work.EQ

open Filter _root_.Topology Complex Metric

noncomputable section

/-- The **candidate chain family** attached to the two words `ε` (stable), `η` (unstable), the
sign list `s` of the `N` backward steps (`N > 0`), and the value `C ≠ 0`: the chain whose
`ψ₁`-coordinate is `z` and whose `ψ₂`-coordinate is `C/z`, so that its invariant parameter is
constantly `C`. -/
def candFam (a : ℝ) (h : ℂ → ℂ) (ε η s : List Bool) (N : ℕ) (C : ℂ) : ℂ → ℤ → ℂ × ℂ :=
  fun z n => (candChain a h ε η s N C z).1 n

@[simp] theorem candFam_apply (a : ℝ) (h : ℂ → ℂ) (ε η s : List Bool) (N : ℕ) (C : ℂ)
    (z : ℂ) (n : ℤ) : candFam a h ε η s N C z n = (candChain a h ε η s N C z).1 n := rfl

/-- **An analytic family of candidate chains with value `C` yields a regular component of value
`C`.**  This is the "branch counting" conclusion of Rychlik's Theorem 11: the explicit chains
`candChain a h ε η s N C z` have `ψ₁ = z`, `ψ₂ = C/z`, so `ψ ≡ C` along the family; the forward
tail is the principal leaf from depth `N` and the backward one from depth `2N` (`candChain`'s
definition), so `Work.EQ.exists_regular_of_family` applies at depth `2N`. -/
theorem exists_regular_of_candChain {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hU0 : ∀ z ∈ U, z ≠ 0)
    {ε η s : List Bool} {N : ℕ} (hN : 0 < N) {C : ℂ} (hC : C ≠ 0)
    (hε : ε.length = N) (hη : η.length = N) (hs : s.length = N)
    (han : ∀ n : ℤ, AnalyticOnNhd ℂ (fun z => (candChain a h ε η s N C z).1 n) U)
    (hchain : ∀ z ∈ U, IsChain a h (candChain a h ε η s N C z))
    (hsmall : ∀ z ∈ U, ‖(eqLam a : ℂ) ^ (2 * N) * z‖ < r ∧
      ‖(eqLam a : ℂ) ^ (2 * N) * (C / z)‖ < r) :
    ∃ p ∈ H0 a h, ∀ q ∈ connectedComponentIn (H0 a h) p, q.2.1 * q.2.2 = C := by
  have hnorm2 : ∀ x : ℝ, ‖((x : ℝ) : ℂ)‖ = |x| := fun x => by simp
  refine exists_regular_of_family (a := a) ha0 ha1 hh hU hUc (m := candFam a h ε η s N C)
    (u := fun z => z) (v := fun z => C / z) (c := C) hC ?_ ?_ ?_ ?_ ?_ ?_ (N := 2 * N) ?_ ?_ ?_
  · intro n
    simpa only [candFam] using han n
  · exact analyticOnNhd_id
  · exact hU0
  · intro z hz
    exact mul_div_cancel₀ C (hU0 z hz)
  · obtain ⟨z₁, hz₁⟩ := hUc.nonempty
    obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.mp hU z₁ hz₁
    have hdist : dist (z₁ + ((e / 2 : ℝ) : ℂ)) z₁ = e / 2 := by
      rw [dist_eq_norm, show z₁ + ((e / 2 : ℝ) : ℂ) - z₁ = ((e / 2 : ℝ) : ℂ) by ring,
        hnorm2, abs_of_pos (by linarith : (0 : ℝ) < e / 2)]
    refine ⟨z₁, hz₁, z₁ + ((e / 2 : ℝ) : ℂ), hball (Metric.mem_ball.mpr ?_), ?_⟩
    · rw [hdist]; linarith
    · intro hcon
      rw [← hcon, dist_self] at hdist
      linarith
  · intro z hz n
    exact ((hchain z hz).1 n).1
  · exact hsmall
  · intro z hz n hn
    have htoNat : ((n : ℤ)).toNat = n := Int.toNat_natCast n
    have h2 : ¬ (n ≤ N) := by omega
    rw [candFam_apply, candChain_fst_apply, if_pos (Int.natCast_nonneg n), htoNat, if_neg h2,
      zpow_natCast]
  · intro z hz n hn
    have htoNat : (-(-(n : ℤ))).toNat = n := by rw [neg_neg, Int.toNat_natCast]
    have h2 : ¬ (n ≤ N) := by omega
    rw [candFam_apply, candChain_fst_apply, if_neg (by omega : ¬ ((0 : ℤ) ≤ -(n : ℤ))), htoNat,
      if_neg h2, List.drop_eq_nil_of_le (by rw [hη]; omega), zpow_natCast]
    rfl

/-! ## The backward image of a fan value is a fan value -/

/-- **The iterated backward image of a fan value is a fan value again.**  With `λ = eqLam a`,
`bwdP a l (fan a h ε u) = fan a h (l.reverse ++ ε) (u/λ^{|l|})`. -/
private theorem bwdP_fan_eq_fan_aux {a : ℝ} (hlam : (eqLam a : ℂ) ≠ 0) (h : ℂ → ℂ) :
    ∀ (l ε : List Bool) (u : ℂ),
      bwdP a l (fan a h ε u) = fan a h (l.reverse ++ ε)
        (u / ((eqLam a : ℝ) : ℂ) ^ l.length) := by
  intro l
  induction l with
  | nil => intro ε u; simp [bwdP]
  | cons s₀ l' ih =>
    intro ε u
    have h1 : bwdP a (s₀ :: l') (fan a h ε u) =
        bwdP a l' (fan a h (s₀ :: ε) (u / ((eqLam a : ℝ) : ℂ))) := by
      rw [bwdP_cons, fan_cons']
      congr 1
      field_simp
    rw [h1, ih]
    have hL : l'.reverse ++ (s₀ :: ε) = (s₀ :: l').reverse ++ ε := by
      rw [List.reverse_cons, List.append_assoc]
      congr 1
    have hR : (u / ((eqLam a : ℝ) : ℂ)) / (((eqLam a : ℝ) : ℂ) ^ l'.length)
        = u / (((eqLam a : ℝ) : ℂ) ^ (s₀ :: l').length) := by
      rw [List.length_cons, div_div, pow_succ]
      ring
    rw [hL, hR]

/-! ## Words of length `N` -/

/-- The finset of words of length `N`. -/
def wordsOfLength (N : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin N → Bool)).image List.ofFn

theorem mem_wordsOfLength {N : ℕ} {l : List Bool} : l ∈ wordsOfLength N ↔ l.length = N := by
  constructor
  · intro h
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp h
    simpa using List.length_ofFn (f := f)
  · intro h
    subst h
    exact Finset.mem_image.mpr ⟨fun i => l.get i, Finset.mem_univ _, List.ofFn_get l⟩

/-- A closed annulus in `ℂ` with `0 < r₁` is compact. -/
theorem isCompact_closedAnnulus {r₁ r₂ : ℝ} : IsCompact {z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂} := by
  have hclosed : IsClosed {z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂} := by
    have h1 : IsClosed {z : ℂ | r₁ ≤ ‖z‖} := isClosed_le continuous_const continuous_norm
    have h2 : IsClosed {z : ℂ | ‖z‖ ≤ r₂} := isClosed_le continuous_norm continuous_const
    have heq : {z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂} = {z : ℂ | r₁ ≤ ‖z‖} ∩ {z : ℂ | ‖z‖ ≤ r₂} := by
      ext z; exact Iff.rfl
    rw [heq]
    exact h1.inter h2
  refine isCompact_iff_isClosed_bounded.mpr ⟨hclosed, ?_⟩
  rw [isBounded_iff_subset_closedBall (0 : ℂ)]
  refine ⟨r₂, ?_⟩
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hz.2
/-! ## Analyticity of the candidate-chain coordinates -/

/-- Analyticity of a fan map composed with an analytic function taking values in the fan disc. -/
theorem analyticOnNhd_fan_comp {a : ℝ} {h : ℂ → ℂ} {Ke Lam Q δf : ℝ}
    (hFG : ∀ (ε' : List Bool) (v : ℂ), ‖v‖ < δf → FanGood a h Ke Lam Q ε' v)
    {U : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : ∀ z ∈ U, ‖g z‖ < δf) (ε' : List Bool) :
    AnalyticOnNhd ℂ (fun z => fan a h ε' (g z)) U := by
  have hf : AnalyticOnNhd ℂ (fan a h ε') (Metric.ball 0 δf) :=
    fun v hv => (hFG ε' v (by rwa [Metric.mem_ball, dist_zero_right] at hv)).1
  have h := hf.comp hg (fun z hz => by
    rw [Metric.mem_ball, dist_zero_right]; exact hmaps z hz)
  simpa [Function.comp_def] using h

/-- **Analyticity of the backward iterates of a fan map.**  With `δf` the fan radius of the
uniform estimates (`FanGood`), on any open `U` with `‖z‖ < δf * λ^N` the map
`z ↦ bwdP a (s.take m) (fan a h ε z)` is analytic for every `m ≤ N`, provided `N ≤ s.length`. -/
theorem analyticOnNhd_bwdP_fan_of {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {Ke Lam Q δf : ℝ} (hδf : 0 < δf)
    (hFG : ∀ (ε' : List Bool) (v : ℂ), ‖v‖ < δf → FanGood a h Ke Lam Q ε' v)
    {N : ℕ} {ε s : List Bool} (hs : N ≤ s.length) {U : Set ℂ} (hU : IsOpen U)
    (hUz : ∀ z ∈ U, ‖z‖ < δf * (eqLam a) ^ N) :
    ∀ m : ℕ, m ≤ N → AnalyticOnNhd ℂ (fun z => bwdP a (s.take m) (fan a h ε z)) U := by
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hlamne : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam0)
  intro m hm
  have htake : (s.take m).length = m := by
    rw [List.length_take, Nat.min_eq_left (le_trans hm hs)]
  have hfun : (fun z => bwdP a (s.take m) (fan a h ε z))
      = fun z => fan a h ((s.take m).reverse ++ ε) (z / ((eqLam a : ℝ) : ℂ) ^ m) := by
    funext z
    rw [bwdP_fan_eq_fan_aux hlamne h (s.take m) ε z, htake]
  rw [hfun]
  refine analyticOnNhd_fan_comp hFG ?_ ?_ _
  · exact fun z hz => AnalyticAt.div_const (c := ((eqLam a : ℝ) : ℂ) ^ m) analyticAt_id
  · intro z hz
    rw [norm_div]
    have hmpos : 0 < (eqLam a) ^ m := pow_pos hlam0 m
    have hnorm1 : ‖((eqLam a : ℝ) : ℂ)‖ = eqLam a := by
      rw [show ‖((eqLam a : ℝ) : ℂ)‖ = |eqLam a| from by simp]
      exact abs_of_pos hlam0
    have hnorm : ‖((eqLam a : ℝ) : ℂ) ^ m‖ = (eqLam a) ^ m := by
      rw [norm_pow, hnorm1]
    rw [hnorm, div_lt_iff₀ hmpos]
    exact lt_of_lt_of_le (hUz z hz)
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hlam0.le hlam1.le hm) (le_of_lt hδf))
/-! ## Reading the candidate chains over an annulus -/

/-- Norm of a real power of `eqLam a`. -/
theorem norm_zpow_eqLam {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℤ) :
    ‖((eqLam a : ℝ) : ℂ) ^ n‖ = (eqLam a) ^ n := by
  rw [norm_zpow]
  congr 1
  rw [show ‖((eqLam a : ℝ) : ℂ)‖ = |eqLam a| from by simp, abs_of_pos (eqLam_pos' ha0 ha1)]

/-- Norm of a natural power of `eqLam a`. -/
theorem norm_pow_eqLam {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    ‖((eqLam a : ℝ) : ℂ) ^ n‖ = (eqLam a) ^ n := by
  rw [norm_pow]
  congr 1
  rw [show ‖((eqLam a : ℝ) : ℂ)‖ = |eqLam a| from by simp, abs_of_pos (eqLam_pos' ha0 ha1)]

/-- A nonnegative integer power of a number in `[0,1]` is at most `1`. -/
theorem zpow_le_one_of_nonneg {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {n : ℤ} (hn : 0 ≤ n) :
    a ^ n ≤ 1 := by
  rw [show a ^ n = a ^ n.toNat from by
    rw [← zpow_natCast a n.toNat, Int.toNat_of_nonneg hn]]
  exact pow_le_one₀ ha0 ha1

/-- **Branch counting (Rychlik Thm 11, step 5).** -/
theorem exists_regular_of_readable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (N : ℕ) (hN : 0 < N) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : r₂ < δ₀)
      {ε η : List Bool} (hε : ε.length = N) (hη : η.length = N) {C : ℂ} (hC : C ≠ 0)
      (hCr : ‖C‖ / r₁ ≤ δ₀)
      (hcount : ¬ ({z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ ∧ ∃ s : List Bool, s.length = N ∧
        bwdP a s (fan a h ε z) =
          eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / z)))}).Countable),
      ∃ p ∈ H0 a h, ∀ q ∈ connectedComponentIn (H0 a h) p, q.2.1 * q.2.2 = C := by
  obtain ⟨Ke, Lam, Q, δf, hKe, hLam, hQ, hδf, hFG₀⟩ := fan_induction ha0 ha1 hh
  obtain ⟨ρg, hρg, hgan, hg0, hgreg, hginj, hgd⟩ := germC_facts ha0 ha1 hh
  have hFG : ∀ (ε' : List Bool) (v : ℂ), ‖v‖ < δf → FanGood a h Ke Lam Q ε' v :=
    fun ε' v hv => hFG₀ ε' v (by rw [Metric.mem_ball, dist_zero_right]; exact hv)
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hlamne : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam0)
  have hr : 0 < r := hh.1
  have hlamN : 0 < (eqLam a) ^ N := pow_pos hlam0 N
  have hlam2N : 0 < (eqLam a) ^ (2 * N) := pow_pos hlam0 _
  have hlamNle : (eqLam a) ^ N ≤ 1 := pow_le_one₀ hlam0.le hlam1.le
  have hlamNlt : (eqLam a) ^ N < 1 := pow_lt_one₀ hlam0.le hlam1 hN.ne'
  set δ₀ : ℝ := min (min δf ρg * ((eqLam a) ^ N / 2)) (min (ρg / 2)
      (min (r / (4 * (eqLam a) ^ (2 * N))) 1)) with hδ₀def
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def]
    exact lt_min (mul_pos (lt_min hδf hρg) (by positivity))
      (lt_min (by linarith) (lt_min (div_pos hr (by positivity)) one_pos))
  have hδ₀_le_small : 2 * δ₀ ≤ min δf ρg * (eqLam a) ^ N := by
    have h : δ₀ ≤ min δf ρg * ((eqLam a) ^ N / 2) := by rw [hδ₀def]; exact min_le_left _ _
    linarith
  have hδ₀_le_ρg : 2 * δ₀ ≤ ρg := by
    have h : δ₀ ≤ ρg / 2 := by
      rw [hδ₀def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hδ₀_lt_r : 2 * δ₀ * (eqLam a) ^ (2 * N) < r := by
    have h : δ₀ ≤ r / (4 * (eqLam a) ^ (2 * N)) := by
      rw [hδ₀def]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * (eqLam a) ^ (2 * N))] at h
    linarith
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro r₁ r₂ hr₁ hr₂ ε η hε hη C hC hCr hcount
  set G : ℂ → ℂ × ℂ := fun z => eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / z)))
    with hGdef
  obtain ⟨s, hsl, hsc⟩ : ∃ s ∈ (wordsOfLength N : Set (List Bool)),
      ¬ ({z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ ∧ bwdP a s (fan a h ε z) = G z}).Countable := by
    by_contra hc
    push_neg at hc
    refine hcount (Set.Countable.mono ?_ (Set.Countable.biUnion
      (wordsOfLength N).finite_toSet.countable (fun s hs => hc s hs)))
    rintro z ⟨hz1, hz2, s, hsl, hs⟩
    exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨mem_wordsOfLength.mpr hsl, hz1, hz2, hs⟩⟩
  have hsN : s.length = N := mem_wordsOfLength.mp hsl
  set Z : Set ℂ := {z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ ∧ bwdP a s (fan a h ε z) = G z} with hZdef
  have hZinf : Z.Infinite := fun hfin => hsc hfin.countable
  obtain ⟨z₀, hz₀K, hz₀acc⟩ :=
    hZinf.exists_accPt_of_subset_isCompact isCompact_closedAnnulus (fun z hz => ⟨hz.1, hz.2.1⟩)
  set ρ : ℝ := min δ₀ (r₁ / 4) with hρdef
  have hρpos : 0 < ρ := lt_min hδ₀pos (by linarith)
  have hρδ₀ : ρ ≤ δ₀ := min_le_left _ _
  have hρr₁ : ρ ≤ r₁ / 4 := min_le_right _ _
  have hzlow : ∀ z ∈ Metric.ball z₀ ρ, 3 * r₁ / 4 ≤ ‖z‖ := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 : ‖z₀‖ ≤ ‖z - z₀‖ + ‖z‖ := by
      have h2 : ‖z₀‖ = ‖(z₀ - z) + z‖ := by congr 1; ring
      rw [h2]
      exact le_trans (norm_add_le _ _) (le_of_eq (by rw [norm_sub_rev]))
    linarith [le_of_lt hz, hz₀K.1, hρr₁]
  have hzlt : ∀ z ∈ Metric.ball z₀ ρ, ‖z‖ < 2 * δ₀ := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
      have h2 : ‖z‖ = ‖(z - z₀) + z₀‖ := by congr 1; ring
      rw [h2]
      exact norm_add_le _ _
    linarith [le_of_lt hz, hz₀K.2, hρδ₀, hr₂]
  have hczlt : ∀ z ∈ Metric.ball z₀ ρ, ‖C / z‖ < 2 * δ₀ := by
    intro z hz
    rw [norm_div]
    have h2 : ‖C‖ / ‖z‖ ≤ ‖C‖ / (3 * r₁ / 4) :=
      div_le_div_of_nonneg_left (norm_nonneg C) (by linarith) (hzlow z hz)
    have h3 : ‖C‖ / (3 * r₁ / 4) = (4 / 3) * (‖C‖ / r₁) := by field_simp
    have h4 : (4 / 3) * (‖C‖ / r₁) ≤ (4 / 3) * δ₀ := by linarith
    have h5 : (4 / 3) * δ₀ < 2 * δ₀ := by linarith
    linarith
  have hzltδf : ∀ z ∈ Metric.ball z₀ ρ, ‖z‖ < δf * (eqLam a) ^ N := by
    intro z hz
    exact lt_of_lt_of_le (hzlt z hz)
      (le_trans hδ₀_le_small (mul_le_mul_of_nonneg_right (min_le_left _ _) hlamN.le))
  have hczltδf : ∀ z ∈ Metric.ball z₀ ρ, ‖C / z‖ < δf * (eqLam a) ^ N := by
    intro z hz
    exact lt_of_lt_of_le (hczlt z hz)
      (le_trans hδ₀_le_small (mul_le_mul_of_nonneg_right (min_le_left _ _) hlamN.le))
  have hδ₀_le_min : 2 * δ₀ ≤ min δf ρg :=
    le_trans hδ₀_le_small (by
      calc min δf ρg * (eqLam a) ^ N ≤ min δf ρg * 1 :=
            mul_le_mul_of_nonneg_left hlamNle (le_of_lt (lt_min hδf hρg))
        _ = min δf ρg := mul_one _)
  have hzb : ∀ z ∈ Metric.ball z₀ ρ, ‖z‖ < min δf ρg * (eqLam a) ^ N :=
    fun z hz => lt_of_lt_of_le (hzlt z hz) hδ₀_le_small
  have hczb : ∀ z ∈ Metric.ball z₀ ρ, ‖C / z‖ < min δf ρg * (eqLam a) ^ N :=
    fun z hz => lt_of_lt_of_le (hczlt z hz) hδ₀_le_small
  have hzltρg : ∀ z ∈ Metric.ball z₀ ρ, ‖z‖ < ρg :=
    fun z hz => lt_of_lt_of_le (hzlt z hz) hδ₀_le_ρg
  have hczltρg : ∀ z ∈ Metric.ball z₀ ρ, ‖C / z‖ < ρg :=
    fun z hz => lt_of_lt_of_le (hczlt z hz) hδ₀_le_ρg
  have hballne : ∀ z ∈ Metric.ball z₀ ρ, z ≠ 0 := by
    intro z hz h0
    have h := hzlow z hz
    rw [h0, norm_zero] at h
    linarith
  have hreg' : ∀ u : ℂ, ‖u‖ < ρg → RegPair a (germC a h u) (germC a h ((eqLam a : ℂ) * u)) :=
    fun u hu => (hgreg u (by rw [Metric.mem_ball, dist_zero_right]; exact hu)).1
  -- analyticity of the two ends
  have hFana : AnalyticOnNhd ℂ (fun z => bwdP a s (fan a h ε z)) (Metric.ball z₀ ρ) := by
    have h := analyticOnNhd_bwdP_fan_of (ε := ε) ha0 ha1 hh hδf hFG (le_of_eq hsN.symm)
      Metric.isOpen_ball hzltδf N le_rfl
    rwa [List.take_of_length_le (le_of_eq hsN)] at h
  have hGana : AnalyticOnNhd ℂ G (Metric.ball z₀ ρ) := by
    rw [hGdef]
    have h1 : AnalyticOnNhd ℂ (fun z => fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / z)))
        (Metric.ball z₀ ρ) := by
      refine analyticOnNhd_fan_comp hFG ?_ ?_ η
      · refine fun z hz => ?_
        have hdiv : AnalyticAt ℂ (fun w : ℂ => C / w) z :=
          AnalyticAt.div analyticAt_const analyticAt_id (hballne z hz)
        exact analyticAt_const.mul hdiv
      · intro z hz
        rw [norm_mul, norm_pow_eqLam ha0 ha1 N]
        calc (eqLam a) ^ N * ‖C / z‖ ≤ 1 * (δf * (eqLam a) ^ N) :=
              mul_le_mul hlamNle (le_of_lt (hczltδf z hz)) (norm_nonneg _) zero_le_one
          _ = δf * (eqLam a) ^ N := one_mul _
          _ < δf := by nlinarith [hlamNlt, hδf]
    refine fun z hz => ?_
    have h2 : AnalyticAt ℂ (fun z : ℂ => eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / z)))) z :=
      (analyticAt_eqMirror _).comp (h1 z hz)
    exact h2
  have hfreqZ : ∃ᶠ y in 𝓝[≠] z₀, y ∈ Z := by
    rw [frequently_mem_iff_neBot]
    exact hz₀acc
  have hfreq : ∃ᶠ y in 𝓝[≠] z₀, bwdP a s (fan a h ε y) = G y :=
    hfreqZ.mono (fun y hy => by rw [hZdef] at hy; exact hy.2.2)
  have hclos : z₀ ∈ closure ({z : ℂ | bwdP a s (fan a h ε z) = G z} \ {z₀}) :=
    mem_closure_ne_iff_frequently_within.mpr hfreq
  have hEqOn : ∀ z ∈ Metric.ball z₀ ρ, bwdP a s (fan a h ε z) = G z :=
    AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure hFana hGana Metric.isPreconnected_ball
      (Metric.mem_ball_self hρpos) hclos
  -- analyticity of the coordinates of the candidate chain
  have hcoord : ∀ n : ℤ, AnalyticOnNhd ℂ (fun z => (candChain a h ε η s N C z).1 n)
      (Metric.ball z₀ ρ) := by
    intro n
    by_cases hn : (0 : ℤ) ≤ n
    · by_cases hnN : n ≤ (N : ℤ)
      · have htoNat : n.toNat ≤ N := by omega
        have hrep : (fun z => (candChain a h ε η s N C z).1 n)
            = fun z => fan a h (ε.drop n.toNat) (((eqLam a : ℝ) : ℂ) ^ n * z) := by
          funext z
          rw [candChain_fst_apply, if_pos hn, if_pos htoNat]
        rw [hrep]
        refine analyticOnNhd_fan_comp hFG ?_ ?_ _
        · exact fun z hz => analyticAt_const.mul analyticAt_id
        · intro z hz
          rw [norm_mul, norm_zpow_eqLam ha0 ha1 n]
          have hpow : (eqLam a) ^ n ≤ 1 := zpow_le_one_of_nonneg hlam0.le hlam1.le hn
          calc (eqLam a) ^ n * ‖z‖ ≤ 1 * (δf * (eqLam a) ^ N) :=
                mul_le_mul hpow (le_of_lt (hzltδf z hz)) (norm_nonneg _) zero_le_one
            _ = δf * (eqLam a) ^ N := one_mul _
            _ < δf := by nlinarith [hlamNlt, hδf]
      · have hrep : (fun z => (candChain a h ε η s N C z).1 n)
            = fun z => germC a h (((eqLam a : ℝ) : ℂ) ^ n * z) := by
          funext z
          rw [candChain_fst_apply, if_pos hn, if_neg (by omega : ¬ (n.toNat ≤ N))]
        rw [hrep]
        refine fun z hz => ?_
        have hmem : ((eqLam a : ℝ) : ℂ) ^ n * z ∈ Metric.ball 0 ρg := by
          rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_zpow_eqLam ha0 ha1 n]
          have hpow : (eqLam a) ^ n ≤ 1 := zpow_le_one_of_nonneg hlam0.le hlam1.le hn
          calc (eqLam a) ^ n * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hpow (norm_nonneg z)
            _ = ‖z‖ := one_mul _
            _ < 2 * δ₀ := hzlt z hz
            _ ≤ ρg := hδ₀_le_ρg
        exact (hgan _ hmem).comp (analyticAt_const.mul analyticAt_id)
    · have hnneg : n < 0 := by omega
      by_cases hnn : (-n) ≤ (N : ℤ)
      · have hle : (-n).toNat ≤ N := by omega
        have hrep : (fun z => (candChain a h ε η s N C z).1 n)
            = fun z => bwdP a (s.take (-n).toNat) (fan a h ε z) := by
          funext z
          rw [candChain_fst_apply, if_neg (by omega : ¬ ((0 : ℤ) ≤ n)), if_pos hle]
        rw [hrep]
        exact analyticOnNhd_bwdP_fan_of ha0 ha1 hh hδf hFG (le_of_eq hsN.symm) Metric.isOpen_ball
          hzltδf _ hle
      · have hle : N < (-n).toNat := by omega
        have hrep : (fun z => (candChain a h ε η s N C z).1 n)
            = fun z => eqMirror (fan a h (η.drop ((-n).toNat - N))
                (((eqLam a : ℝ) : ℂ) ^ ((-n).toNat) * (C / z))) := by
          funext z
          rw [candChain_fst_apply, if_neg (by omega : ¬ ((0 : ℤ) ≤ n)),
            if_neg (by omega : ¬ ((-n).toNat ≤ N)), zpow_natCast]
        rw [hrep]
        have h1 : AnalyticOnNhd ℂ (fun z => fan a h (η.drop ((-n).toNat - N))
            (((eqLam a : ℝ) : ℂ) ^ ((-n).toNat) * (C / z))) (Metric.ball z₀ ρ) := by
          refine analyticOnNhd_fan_comp hFG ?_ ?_ _
          · refine fun z hz => ?_
            have hdiv : AnalyticAt ℂ (fun w : ℂ => C / w) z :=
              AnalyticAt.div analyticAt_const analyticAt_id (hballne z hz)
            exact analyticAt_const.mul hdiv
          · intro z hz
            rw [norm_mul, norm_pow_eqLam ha0 ha1 ((-n).toNat)]
            have hpow : (eqLam a) ^ ((-n).toNat) ≤ 1 := pow_le_one₀ hlam0.le hlam1.le
            calc (eqLam a) ^ ((-n).toNat) * ‖C / z‖ ≤ 1 * ‖C / z‖ :=
                  mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
              _ = ‖C / z‖ := one_mul _
              _ < 2 * δ₀ := hczlt z hz
              _ ≤ min δf ρg := hδ₀_le_min
              _ ≤ δf := min_le_left _ _
        refine fun z hz => ?_
        have h2 : AnalyticAt ℂ (fun z : ℂ => eqMirror (fan a h (η.drop ((-n).toNat - N))
            (((eqLam a : ℝ) : ℂ) ^ ((-n).toNat) * (C / z)))) z :=
          (analyticAt_eqMirror _).comp (h1 z hz)
        exact h2
  -- assemble
  refine exists_regular_of_family ha0 ha1 hh Metric.isOpen_ball
    ((convex_ball z₀ ρ).isConnected ⟨z₀, Metric.mem_ball_self hρpos⟩)
    (m := candFam a h ε η s N C) (u := fun z => z) (v := fun z => C / z) (c := C) hC ?_ ?_ ?_ ?_
    ?_ ?_ (N := 2 * N) ?_ ?_ ?_
  · intro n
    simpa only [candFam] using hcoord n
  · exact analyticOnNhd_id
  · intro z hz
    exact hballne z hz
  · intro z hz
    exact mul_div_cancel₀ C (hballne z hz)
  · obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball z₀ (Metric.mem_ball_self hρpos)
    have hnorm2 : ∀ x : ℝ, ‖((x : ℝ) : ℂ)‖ = |x| := fun x => by simp
    have hnorm : ‖((e / 2 : ℝ) : ℂ)‖ = e / 2 := by
      rw [hnorm2, abs_of_pos (by linarith : (0 : ℝ) < e / 2)]
    have hdist : dist (z₀ + ((e / 2 : ℝ) : ℂ)) z₀ = e / 2 := by
      rw [dist_eq_norm, show z₀ + ((e / 2 : ℝ) : ℂ) - z₀ = ((e / 2 : ℝ) : ℂ) by ring, hnorm]
    refine ⟨z₀, Metric.mem_ball_self hρpos, z₀ + ((e / 2 : ℝ) : ℂ), hball (Metric.mem_ball.mpr ?_),
      ?_⟩
    · rw [hdist]; linarith
    · intro hcon
      rw [← hcon, dist_self] at hdist
      linarith
  · intro z hz n
    have hjn : bwdP a s (fan a h ε z) = eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / z))) :=
      hEqOn z hz
    exact eqRelC_candChain ha0 ha1 hh hN hε hη hsN hFG hreg' (hzb z hz) (hczb z hz) hjn n
  · intro z hz
    refine ⟨?_, ?_⟩
    · rw [norm_mul, norm_pow_eqLam ha0 ha1 (2 * N)]
      calc (eqLam a) ^ (2 * N) * ‖z‖ ≤ (eqLam a) ^ (2 * N) * (2 * δ₀) :=
            mul_le_mul_of_nonneg_left (le_of_lt (hzlt z hz)) (by positivity)
        _ = 2 * δ₀ * (eqLam a) ^ (2 * N) := by ring
        _ < r := hδ₀_lt_r
    · rw [norm_mul, norm_pow_eqLam ha0 ha1 (2 * N)]
      calc (eqLam a) ^ (2 * N) * ‖C / z‖ ≤ (eqLam a) ^ (2 * N) * (2 * δ₀) :=
            mul_le_mul_of_nonneg_left (le_of_lt (hczlt z hz)) (by positivity)
        _ = 2 * δ₀ * (eqLam a) ^ (2 * N) := by ring
        _ < r := hδ₀_lt_r
  · intro z hz n hn
    rw [candFam_apply, candChain_fst_apply]
    have htoNat : ((n : ℤ)).toNat = n := Int.toNat_natCast n
    have h2 : ¬ (n ≤ N) := by omega
    rw [if_pos (Int.natCast_nonneg n), htoNat, if_neg h2, zpow_natCast]
  · intro z hz n hn
    rw [candFam_apply, candChain_fst_apply]
    have htoNat : (-(-(n : ℤ))).toNat = n := by rw [neg_neg, Int.toNat_natCast]
    have h2 : ¬ (n ≤ N) := by omega
    rw [if_neg (by omega : ¬ ((0 : ℤ) ≤ -(n : ℤ))), htoNat, if_neg h2,
      List.drop_eq_nil_of_le (by rw [hη]; omega), zpow_natCast]
    rfl

end

end Work.EQ

/-!
# State of `Work.EQ.H0_reg_wset` (end of the session that proved `exists_regular_of_readable`)

## What is here (all sorry-free; `eqRelC_candChain` is a colleague's pending child)

* `candFam` — the candidate-chain family `z ↦ (candChain a h ε η s N C z).1`;
* `exists_regular_of_candChain` — an analytic family of candidate chains with value `C` (and the
  cone conditions) yields a *regular* component of value `C`, via `Work.EQ.exists_regular_of_family`
  at depth `2N`;
* `bwdP_fan_eq_fan_aux` — `bwdP a l (fan a h ε u) = fan a h (l.reverse ++ ε) (u/λ^{|l|})`;
* `wordsOfLength`, `mem_wordsOfLength`, `isCompact_closedAnnulus`;
* `analyticOnNhd_fan_comp`, `analyticOnNhd_bwdP_fan_of` — analyticity of fan maps and of their
  backward iterates (proved from the uniform fan estimates `FanGood`; deliberately *not* importing
  `Work.EQ.analyticOnNhd_candChain` or `Work.EQ.no_near_axis_segment`, both of which import
  `no_near_axis_segment`, which clashes with `H0_section_local`'s `Work.EQ.norm_sub_le_add`);
* `norm_zpow_eqLam`, `norm_pow_eqLam`, `zpow_le_one_of_nonneg`;
* **`exists_regular_of_readable`** — this session's main result: *branch counting*.  For a compact
  annulus `{r₁ ≤ ‖z‖ ≤ r₂}` with `r₂` small and `‖C‖/r₁` small, if uncountably many `z` admit a sign
  list `s` of length `N` with `bwdP a s (fan a h ε z) = eqMirror (fan a h η (λ^N (C/z)))`, then `C`
  is the value of a regular component.  Proof: the annulus is compact, so a fixed sign list works on
  an infinite set `Z` accumulating at `z₀`; the identity theorem
  (`AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure`) extends the junction identity to a disc `U`,
  `eqRelC_candChain` supplies `EqRelC` at every step on `U`, and `exists_regular_of_family` finishes.

## What is still missing for `Work.EQ.H0_regular`

1. **Step 5a (the covering), and it is the crux.**  Needed: from the uncountable shifted cluster set
   `Z_A` of `Work.EQ.not_countable_shiftClusterSet_of_good_ray` produce *one* uncountable class
   `W(ε, η, μ₁, μ₂)` of the shape above (with `C = c₀ μ₁ μ₂`).  A first attempt at this statement
   (`Work.EQ.readable_of_shiftCluster`) was **rejected in review** with the correct diagnosis:
   * the depth-`N` reading `x.1 0 = fan a h ε (ψ₁ x)`, `x.1 (-N) = eqMirror (fan a h η (λ^N ψ₂ x))`
     is available only when the tails of `x` are principal from `N`/`2N`
     (`Work.EQ.chain_eq_candChain_of_tails`), and *no hypothesis on `Z_A` gives that*; one needs the
     Thm 8(3)-style uniform tail bound over an annulus `r₂/r₁ > 1/λ` (in the workspace:
     `Work.EQ.H0_tail_bounded` is only local; the global statement is the open `exists_compact_regular_cycle`
     / `la_tail_bound_value` area);
   * forcing `ε.length = η.length = N` makes `fan_trichotomy` case (ii)
     (`ε₀ ++ true^{s_k} ++ C_k`, `s_k → ∞`) impossible, so the case-(ii) scales `μ₁, μ₂ < 1` cannot be
     captured; the `W`-classes of Rychlik §7.7 use *arbitrary-length* limit words, i.e. the class must
     be indexed by `(ε, η, μ₁, μ₂)` with `ε, η : List Bool` free and the segment length `N` the shift
     difference, not the word length.  Recommended shape: index the class by the *segment* (a
     `RegPair`-linked `ℂ × ℂ`-valued tuple of length `N+1`) with endpoints `fan a h ε (μ₁ z)` and
     `eqMirror (fan a h η (λ^N (μ₂ c₀ / z)))`, `ε, η` arbitrary finite words (countably many) and
     `μ₁, μ₂ ∈ Work.EQ.charValSet`;
   * the limit segment is then obtained by `fan_trichotomy` on the two word sequences plus the
     stabilisation of the (finitely many) backward sign lists; case (iii) is refuted by
     `Work.EQ.LaNnas.no_near_axis_segment` (the *clash-free copy* — `no_near_axis_segment` itself
     cannot be imported next to `H0_section_local`).
2. **Step 2 (puncture values countable)**: delegated as `Work.EQ.countable_puncture_values`.
3. **The assembly**: `Work.EQ.H0_component_uniformization` (proved) + `Work.EQ.plane_cover_const`
   (proved) for the `ℂ`-cover case; in the `ℍ`-cover case take the disc cover
   (`Work.EQ.exists_disc_covering_of_uhp`), apply `Work.EQ.good_ray_data` with `L` from step 2 and
   `Work.EQ.fatouRiesz_holds`, use `Work.EQ.not_countable_good_values` for the uncountability of the
   good values, `Work.EQ.not_countable_shiftClusterSet_of_good_ray` (with the path-limit dichotomy
   `Work.EQ.H0_path_limit_Iio`) for the uncountable `Z_A`, then step 5a + `exists_regular_of_readable`
   to put every good value in the countable set `C_reg · (M·M)⁻¹`
   (`Work.EQ.countable_regular_values`, `Work.EQ.countable_charValSet`).  The annulus radii must be
   chosen so that `r₂ < δ₀` and `‖C‖/r₁ ≤ δ₀` with `C = c₀μ₁μ₂`; since `‖μ‖ ≤ 1` for
   `μ ∈ charValSet` (`Work.EQ.charVal_props`) and the normalisation `λ^N c₀/z ∈ A` gives
   `λ^N ‖c₀‖ ≈ r₁ r₂`, this is satisfiable by taking `N` large and `r₂ < δ₀`.
-/

