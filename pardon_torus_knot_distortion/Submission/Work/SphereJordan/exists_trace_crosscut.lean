import Mathlib
import Submission.Work.SphereJordan.chamberDefs
import Submission.Work.SphereJordan.gammaInjOnArc
import Submission.Work.SphereJordan.exteriorGermSetup

/-!
# The crosscut of the trace through an interior point of a ball

Let `γ` be a simple closed plane curve, `p` a point, `ε > 0` and `z` a point of `γ.trace` lying in
`Metric.ball p ε`, with the trace *leaving* `Metric.closedBall p ε`.  Then the connected component of
`z` in the part `γ.trace ∩ Metric.ball p ε` of the trace inside the ball is an arc: it is the image of
an injective continuous map `κ` from `[0,1]`, whose interior is mapped into the ball, whose two
endpoints lie on the sphere `Metric.sphere p ε`, and whose range lies in `γ.trace`.

The proof runs in parameters.  The set `{t | ‖γ t - p‖ < ε}` is open in `ℝ` and `2π`-periodic; the
component `K` of `t₀` (a parameter of `z`) in it is an open interval `(a,b)` (the extraction of the
endpoints is `exists_crosscut_of_ball`, a variant of the crosscut extraction of the sibling file
`Work.SphereJordan.germSideComponentCrux`), with `b - a < 2π`, with `‖γ a - p‖ = ‖γ b - p‖ = ε` and
with `γ` injective on `[a,b]`.  The parametrisation is then `κ s = γ (a + s (b - a))`; the
identification of the component with `γ '' Ioo a b` uses only that the trace is the union of the two
compact arcs `γ '' Icc a b` and `γ '' Icc b (a + 2π)`, which meet exactly in `γ a` and `γ b`.

## Main results

* `Work.SphereJordan.exists_trace_crosscut` — the crosscut parametrisation;
* `Work.SphereJordan.trace_eq_image_Icc_add` — the trace is the image of any window of length `2π`;
* `Work.SphereJordan.exists_crosscut_of_ball` — the crosscut extraction in parameters.
-/

open Set Metric

namespace Work.SphereJordan

theorem exists_int_shift_mem_Icc_period {a T x : ℝ} (hT : 0 < T) :
    ∃ k : ℤ, a + (x + (k : ℝ) * T) ∈ Set.Icc (a - T / 2) (a + T / 2) := by
  set z : ℝ := x / T + 1 / 2 with hz
  have h1 : (⌊z⌋ : ℝ) ≤ x / T + 1 / 2 := by
    have := Int.floor_le z; rw [hz] at this; exact this
  have h2 : x / T + 1 / 2 < (⌊z⌋ : ℝ) + 1 := by
    have := Int.lt_floor_add_one z; rw [hz] at this; exact this
  have hxT : x / T * T = x := div_mul_cancel₀ x (ne_of_gt hT)
  refine ⟨-⌊z⌋, ?_⟩
  constructor
  · push_cast; nlinarith [h1, hxT, hT]
  · push_cast; nlinarith [h2, hxT, hT]

/-- **Crosscut extraction from the preimage of a ball.**  If a trace point `γ t₀` lies strictly inside
`Metric.ball c ρ` and some trace point is at distance `> ρ` from `c` (which forces `ρ > 0`), then the connected component of `t₀` in `{t | ‖γ t - c‖ < ρ}` is an
open interval `(a,b)` whose image is a crosscut of `Metric.ball c ρ`: `a < t₀ < b`, `b - a < 2π`,
`‖γ t - c‖ < ρ` on `(a,b)`, `‖γ t - c‖ ≤ ρ` on `[a,b]`, `‖γ a - c‖ = ‖γ b - c‖ = ρ`,
`γ a ≠ γ b`, and `γ` is injective on `[a,b]`. -/
theorem exists_crosscut_of_ball {γ : Work.Smooth.Jordan.PlaneCurve} (hγ : γ.IsSimple)
    {c : ℂ} {ρ : ℝ} {t₀ : ℝ} (ht₀ : ‖γ.γ t₀ - c‖ < ρ)
    (hex : ∃ t : ℝ, ρ < ‖γ.γ t - c‖) :
    ∃ a b : ℝ, a < t₀ ∧ t₀ < b ∧ b - a < 2 * Real.pi ∧ γ.γ a ≠ γ.γ b ∧
      (∀ t ∈ Set.Ioo a b, ‖γ.γ t - c‖ < ρ) ∧
      (∀ t ∈ Set.Icc a b, ‖γ.γ t - c‖ ≤ ρ) ∧
      ‖γ.γ a - c‖ = ρ ∧ ‖γ.γ b - c‖ = ρ ∧
      Set.InjOn γ.γ (Set.Icc a b) := by
  classical
  set f : ℝ → ℝ := fun t => ‖γ.γ t - c‖ with hf
  have hfcont : Continuous f := by rw [hf]; exact (γ.cont.sub continuous_const).norm
  have hfper : Function.Periodic f (2 * Real.pi) := by
    intro t
    show ‖γ.γ (t + 2 * Real.pi) - c‖ = ‖γ.γ t - c‖
    rw [γ.periodic]
  set P : Set ℝ := {t : ℝ | f t < ρ} with hP
  have hPopen : IsOpen P := isOpen_lt hfcont continuous_const
  have hmemP : ∀ t : ℝ, t ∈ P ↔ f t < ρ := fun t => Iff.rfl
  have ht₀P : t₀ ∈ P := by rw [hmemP]; simpa only [hf] using ht₀
  set K : Set ℝ := connectedComponentIn P t₀ with hK
  have ht₀K : t₀ ∈ K := mem_connectedComponentIn ht₀P
  have hKconn : IsPreconnected K := isPreconnected_connectedComponentIn
  have hKord : K.OrdConnected := hKconn.ordConnected
  have hKsub : K ⊆ P := connectedComponentIn_subset P t₀
  have hKne : K.Nonempty := ⟨t₀, ht₀K⟩
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  -- `K` is open (it is a component of the open set `P` inside `ℝ`)
  have hKopen : IsOpen K := by
    rw [isOpen_iff_mem_nhds]
    intro t htK
    obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp
      ((isOpen_iff_mem_nhds.mp hPopen t (hKsub htK)))
    have hI : IsPreconnected (Metric.ball t η) := (convex_ball t η).isPreconnected
    have hconn : IsPreconnected (Metric.ball t η ∪ K) :=
      hI.union t (Metric.mem_ball_self hη) htK hKconn
    have hsub : Metric.ball t η ∪ K ⊆ P := by
      rintro x (hx | hx)
      · exact hηsub hx
      · exact hKsub hx
    have hKsub' : Metric.ball t η ∪ K ⊆ K :=
      hconn.subset_connectedComponentIn (Or.inr ht₀K) hsub
    exact Metric.mem_nhds_iff.mpr ⟨η, hη, fun x hx => hKsub' (Or.inl hx)⟩
  -- a trace parameter outside the ball
  obtain ⟨t₁, ht₁⟩ := hex
  have ht₁P : t₁ ∉ P := by rw [hmemP]; exact not_lt.mpr (le_of_lt ht₁)
  -- bring it (mod `2π`) into the window around `t₀`
  obtain ⟨m, hm⟩ := exists_int_shift_mem_Icc_period (a := t₀) (T := 2 * Real.pi) (x := t₁ - t₀)
    (by positivity)
  set s : ℝ := t₀ + ((t₁ - t₀) + (m : ℝ) * (2 * Real.pi)) with hs
  have hs_eq : s = t₁ + (m : ℝ) * (2 * Real.pi) := by rw [hs]; ring
  have hfs : f s = f t₁ := by rw [hs_eq]; exact hfper.int_mul m t₁
  have hsge : ρ ≤ f s := by rw [hfs]; exact le_of_lt ht₁
  -- the two consecutive points of `s + 2πℤ` straddling `t₀`
  set lo : ℝ := s + ((⌊(t₀ - s) / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) with hlodef
  have hlo_le : lo ≤ t₀ := by
    have h1 : ((⌊(t₀ - s) / (2 * Real.pi)⌋ : ℤ) : ℝ) ≤ (t₀ - s) / (2 * Real.pi) := Int.floor_le _
    have h3 : ((⌊(t₀ - s) / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) ≤ t₀ - s := by
      have h4 := mul_le_mul_of_nonneg_right h1 hpi.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hpi)] at h4
    rw [hlodef]; linarith
  have ht₀_hi : t₀ < lo + 2 * Real.pi := by
    have h1 : (t₀ - s) / (2 * Real.pi) < ((⌊(t₀ - s) / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have h3 : t₀ - s < (((⌊(t₀ - s) / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1) * (2 * Real.pi) := by
      have h4 := mul_lt_mul_of_pos_right h1 hpi
      rwa [div_mul_cancel₀ _ (ne_of_gt hpi)] at h4
    rw [hlodef]; linarith
  have hflo : f lo = f s := by
    have h2 : lo = s + (⌊(t₀ - s) / (2 * Real.pi)⌋ : ℤ) * (2 * Real.pi) := hlodef
    rw [h2]; exact hfper.int_mul _ s
  have hflo_ge : ρ ≤ f lo := hflo ▸ hsge
  have hflo_gt : lo < t₀ := by
    rcases lt_or_eq_of_le hlo_le with h | h
    · exact h
    · exfalso
      have hfe : f lo = f t₀ := by rw [h]
      rw [hfe] at hflo_ge
      have ht₀lt : f t₀ < ρ := by simpa only [hf] using ht₀
      linarith
  -- `K` lies in the open gap `(lo, lo + 2π)`
  have hKg : K ⊆ Set.Ioo lo (lo + 2 * Real.pi) := by
    intro t htK
    rw [Set.mem_Ioo]
    refine ⟨?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      have hmem : lo ∈ K := hKord.out htK ht₀K (Set.mem_Icc.mpr ⟨hcon, hflo_gt.le⟩)
      exact absurd ((hmemP lo).mp (hKsub hmem)) (not_lt.mpr hflo_ge)
    · by_contra hcon
      push Not at hcon
      have hmem : lo + 2 * Real.pi ∈ K :=
        hKord.out ht₀K htK (Set.mem_Icc.mpr ⟨ht₀_hi.le, hcon⟩)
      have hlt : f (lo + 2 * Real.pi) < ρ := (hmemP _).mp (hKsub hmem)
      rw [hflo] at hflo_ge
      rw [hfper lo, hflo] at hlt
      exact absurd hlt (not_lt.mpr hflo_ge)
  have hbdd_below : BddBelow K := ⟨lo, fun x hx => (hKg hx).1.le⟩
  have hbdd_above : BddAbove K := ⟨lo + 2 * Real.pi, fun x hx => (hKg hx).2.le⟩
  set a : ℝ := sInf K with hadef
  set b : ℝ := sSup K with hbdef
  have ha_le : a ≤ t₀ := csInf_le hbdd_below ht₀K
  have ht₀_le : t₀ ≤ b := le_csSup hbdd_above ht₀K
  -- `a, b ∉ K` (openness of `K`)
  have haK : a ∉ K := by
    intro ha
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_iff_mem_nhds.mp hKopen a ha))
    have hle : a ≤ a - δ / 2 := csInf_le hbdd_below (hδsub (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩))
    linarith
  have hbK : b ∉ K := by
    intro hb
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_iff_mem_nhds.mp hKopen b hb))
    have hle : b + δ / 2 ≤ b := le_csSup hbdd_above (hδsub (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩))
    linarith
  have hat₀ : a < t₀ := lt_of_le_of_ne ha_le (fun h => haK (h ▸ ht₀K))
  have ht₀b : t₀ < b := lt_of_le_of_ne ht₀_le (fun h => hbK (h.symm ▸ ht₀K))
  -- `(a,b) ⊆ K`
  have hab_sub : Set.Ioo a b ⊆ K := by
    intro t ht
    obtain ⟨t', ht'K, ht'lt⟩ := exists_lt_of_csInf_lt hKne (by rw [← hadef]; exact ht.1)
    obtain ⟨t'', ht''K, ht''gt⟩ := exists_lt_of_lt_csSup hKne (by rw [← hbdef]; exact ht.2)
    exact hKord.out ht'K ht''K (Set.mem_Icc.mpr ⟨le_of_lt ht'lt, le_of_lt ht''gt⟩)
  have hab : a < b := lt_trans hat₀ ht₀b
  -- the endpoints are not in `P`
  have haP : a ∉ P := by
    intro haP
    obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_iff_mem_nhds.mp hPopen a haP))
    have hsub : Set.Ioo (a - η) b ⊆ P := by
      intro x hx
      rw [Set.mem_Ioo] at hx
      by_cases hxa : x < a
      · exact hηsub (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩)
      · rcases eq_or_lt_of_le (not_lt.mp hxa) with hxeq | hxlt
        · exact hxeq ▸ haP
        · exact hKsub (hab_sub ⟨hxlt, hx.2⟩)
    have hI : IsPreconnected (Set.Ioo (a - η) b) := isPreconnected_Ioo
    have hmem : t₀ ∈ Set.Ioo (a - η) b := ⟨by linarith, ht₀b⟩
    have hsubK : Set.Ioo (a - η) b ⊆ K := hI.subset_connectedComponentIn hmem hsub
    have : a - η / 2 ∈ K := hsubK ⟨by linarith, by linarith⟩
    have hle := csInf_le hbdd_below this
    rw [← hadef] at hle
    linarith
  have hbP : b ∉ P := by
    intro hbP
    obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_iff_mem_nhds.mp hPopen b hbP))
    have hsub : Set.Ioo a (b + η) ⊆ P := by
      intro x hx
      rw [Set.mem_Ioo] at hx
      by_cases hxb : b ≤ x
      · rcases eq_or_lt_of_le hxb with hxeq | hxgt
        · exact hxeq ▸ hbP
        · exact hηsub (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩)
      · exact hKsub (hab_sub ⟨hx.1, not_le.mp hxb⟩)
    have hI : IsPreconnected (Set.Ioo a (b + η)) := isPreconnected_Ioo
    have hmem : t₀ ∈ Set.Ioo a (b + η) := ⟨hat₀, by linarith⟩
    have hsubK : Set.Ioo a (b + η) ⊆ K := hI.subset_connectedComponentIn hmem hsub
    have : b + η / 2 ∈ K := hsubK ⟨by linarith, by linarith⟩
    have hle := le_csSup hbdd_above this
    rw [← hbdef] at hle
    linarith
  have hfa_ge : ρ ≤ f a := not_lt.mp (fun h => haP ((hmemP a).mpr h))
  have hfb_ge : ρ ≤ f b := not_lt.mp (fun h => hbP ((hmemP b).mpr h))
  -- `K = (a,b)`
  have hKeq : K = Set.Ioo a b := by
    refine Set.Subset.antisymm (fun t ht => ?_) hab_sub
    rw [Set.mem_Ioo]
    exact ⟨lt_of_le_of_ne (csInf_le hbdd_below ht) (fun h => haK (h ▸ ht)),
           lt_of_le_of_ne (le_csSup hbdd_above ht) (fun h => hbK (h ▸ ht))⟩
  -- continuity at the endpoints
  have ha_close : a ∈ closure K := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hlt : a < a + ε := by linarith
    obtain ⟨t', ht'K, ht'lt⟩ := exists_lt_of_csInf_lt hKne (by rw [← hadef]; exact hlt)
    have hle : a ≤ t' := csInf_le hbdd_below ht'K
    exact ⟨t', ht'K, by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith⟩
  have hb_close : b ∈ closure K := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨t'', ht''K, ht''gt⟩ :=
      exists_lt_of_lt_csSup hKne (by linarith : b - ε < b)
    have hle : t'' ≤ b := le_csSup hbdd_above ht''K
    exact ⟨t'', ht''K, by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith⟩
  have hclosed : IsClosed {t : ℝ | f t ≤ ρ} := isClosed_le hfcont continuous_const
  have hsub_le : K ⊆ {t : ℝ | f t ≤ ρ} := fun t ht => le_of_lt ((hmemP t).mp (hKsub ht))
  have hfa_le : f a ≤ ρ := hclosed.closure_subset (closure_mono hsub_le ha_close)
  have hfb_le : f b ≤ ρ := hclosed.closure_subset (closure_mono hsub_le hb_close)
  have hfa : f a = ρ := le_antisymm hfa_le hfa_ge
  have hfb : f b = ρ := le_antisymm hfb_le hfb_ge
  -- bounds
  have hlo_a : lo ≤ a := le_csInf hKne (fun x hx => (hKg hx).1.le)
  have hb_hi : b ≤ lo + 2 * Real.pi := csSup_le hKne (fun x hx => (hKg hx).2.le)
  have hab_le : b - a ≤ 2 * Real.pi := by linarith
  have hab_lt : b - a < 2 * Real.pi := by
    rcases lt_or_eq_of_le hab_le with h | h
    · exact h
    · exfalso
      have htrace : γ.trace ⊆ Metric.closedBall c ρ := by
        rintro z ⟨τ, rfl⟩
        obtain ⟨m', hm'⟩ := exists_int_shift_mem_Icc_period (a := a + Real.pi) (T := 2 * Real.pi)
          (x := τ - (a + Real.pi)) (by positivity)
        set τ' : ℝ := (a + Real.pi) + ((τ - (a + Real.pi)) + (m' : ℝ) * (2 * Real.pi)) with hτ'
        have hτ'eq : τ' = τ + (m' : ℝ) * (2 * Real.pi) := by rw [hτ']; ring_nf
        have hτ'per : γ.γ τ' = γ.γ τ := by rw [hτ'eq]; exact γ.periodic.int_mul m' τ
        have hτ'I : τ' ∈ Set.Icc a (a + 2 * Real.pi) := by
          have h1 := hm'.1
          have h2 := hm'.2
          have hπ : (2 * Real.pi) / 2 = Real.pi := by ring
          rw [hτ']
          exact ⟨by linarith [h1, hπ], by linarith [h2, hπ]⟩
        have hb_eq : a + 2 * Real.pi = b := by linarith
        have hτ'Ib : τ' ∈ Set.Icc a b := by rw [← hb_eq]; exact hτ'I
        have hfτ : f τ' ≤ ρ := by
          rcases eq_or_lt_of_le hτ'Ib.1 with h1 | h1
          · rw [← h1]; exact hfa.le
          · rcases eq_or_lt_of_le hτ'Ib.2 with h2 | h2
            · rw [h2]; exact hfb.le
            · exact le_of_lt ((hmemP τ').mp (hKsub (hKeq.symm ▸ ⟨h1, h2⟩)))
        rw [← hτ'per, Metric.mem_closedBall, dist_eq_norm]
        simpa only [hf] using hfτ
      have h2 := htrace (γ.mem_trace t₁)
      rw [Metric.mem_closedBall, dist_eq_norm] at h2
      linarith
  have hne_ab : γ.γ a ≠ γ.γ b := by
    intro hcon
    have h := Work.SphereJordan.gammaInjOn_of_sub_lt hγ ⟨le_refl a, hab.le⟩
      ⟨hab.le, le_refl b⟩ hab_lt hcon
    exact absurd h (ne_of_lt hab)
  exact ⟨a, b, hat₀, ht₀b, hab_lt, hne_ab,
    (fun t ht => by simpa only [hf] using (hmemP t).mp (hKsub (hKeq.symm ▸ ht))),
    (fun t ht => by
      rw [Set.mem_Icc] at ht
      rcases eq_or_lt_of_le ht.1 with h1 | h1
      · rw [← h1]; simpa only [hf] using hfa.le
      · rcases eq_or_lt_of_le ht.2 with h2 | h2
        · rw [h2]; simpa only [hf] using hfb.le
        · exact le_of_lt (by simpa only [hf] using (hmemP t).mp (hKsub (hKeq.symm ▸ ⟨h1, h2⟩)))),
    by simpa only [hf] using hfa, by simpa only [hf] using hfb,
    (fun s₁ hs₁ s₂ hs₂ heq => Work.SphereJordan.gammaInjOn_of_sub_lt hγ hs₁ hs₂ hab_lt heq)⟩

/-! ## The trace in a window of length `2π` -/

/-- **The trace of a `2π`-periodic curve is the image of any window of length `2π`.** -/
theorem trace_eq_image_Icc_add (c : Work.Smooth.Jordan.PlaneCurve) (a : ℝ) :
    c.trace = c.γ '' Set.Icc a (a + 2 * Real.pi) := by
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    obtain ⟨k, hk⟩ := exists_int_shift_mem_Icc_period (a := a + Real.pi) (T := 2 * Real.pi)
      (x := t - (a + Real.pi)) (by positivity)
    refine ⟨t + (k : ℝ) * (2 * Real.pi), ?_, ?_⟩
    · rw [Set.mem_Icc] at hk
      exact Set.mem_Icc.mpr ⟨by linarith [hk.1, Real.pi_pos], by linarith [hk.2, Real.pi_pos]⟩
    · exact c.apply_add_int_mul t k
  · rintro x ⟨t, -, rfl⟩
    exact ⟨t, rfl⟩

/-! ## The crosscut of the trace in a ball -/

theorem exists_trace_crosscut {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple)
    {p : ℂ} {ε : ℝ} {z : ℂ} (hz : z ∈ γ.trace ∩ Metric.ball p ε)
    (hleave : ∃ t : ℝ, γ.γ t ∉ Metric.closedBall p ε) :
    ∃ κ : C(Set.Icc (0 : ℝ) 1, ℂ), Function.Injective κ ∧
      Set.range κ ⊆ γ.trace ∧
      (∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → κ t ∈ Metric.ball p ε) ∧
      (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ≠ (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ∧
      κ ⟨0, by norm_num⟩ ∈ Metric.sphere p ε ∧
      κ ⟨1, by norm_num⟩ ∈ Metric.sphere p ε ∧
      connectedComponentIn (γ.trace ∩ Metric.ball p ε) z =
        κ '' {t : Set.Icc (0 : ℝ) 1 | (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1} := by
  classical
  obtain ⟨θ, hθ⟩ := hz.1
  have hθball : ‖γ.γ θ - p‖ < ε := by
    have h := hz.2
    rw [Metric.mem_ball, dist_eq_norm] at h
    simpa [← hθ] using h
  have hex : ∃ t : ℝ, ε < ‖γ.γ t - p‖ := by
    obtain ⟨t, ht⟩ := hleave
    refine ⟨t, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm] at ht
    exact not_le.mp ht
  obtain ⟨a, b, haθ, hθb, hba, -, hIoo, -, hspa, hspb, hinj⟩ :=
    exists_crosscut_of_ball (γ := γ) hs hθball hex
  have hab : a < b := lt_trans haθ hθb
  have hbapos : 0 < b - a := sub_pos.mpr hab
  -- `b - a < 2π` will be used through the window decomposition `trace = γ '' Icc a b ∪ γ '' Icc b (a+2π)`
  have htrace : γ.trace = γ.γ '' Set.Icc a (a + 2 * Real.pi) := trace_eq_image_Icc_add γ a
  -- the parametrisation of the arc
  have hγcont : Continuous fun s : Set.Icc (0 : ℝ) 1 => γ.γ (a + (s : ℝ) * (b - a)) :=
    γ.cont.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))
  let κ : C(Set.Icc (0 : ℝ) 1, ℂ) := ⟨fun s => γ.γ (a + (s : ℝ) * (b - a)), hγcont⟩
  have hκ : ∀ s : Set.Icc (0 : ℝ) 1, κ s = γ.γ (a + (s : ℝ) * (b - a)) := fun s => rfl
  have hκinj : Function.Injective κ := by
    intro s t hst
    have hs : a + (s : ℝ) * (b - a) ∈ Set.Icc a b :=
      ⟨by nlinarith [s.2.1, hbapos], by nlinarith [s.2.2, hbapos]⟩
    have ht : a + (t : ℝ) * (b - a) ∈ Set.Icc a b :=
      ⟨by nlinarith [t.2.1, hbapos], by nlinarith [t.2.2, hbapos]⟩
    have heq : γ.γ (a + (s : ℝ) * (b - a)) = γ.γ (a + (t : ℝ) * (b - a)) := by
      have h := hst
      rwa [hκ s, hκ t] at h
    have h2 := hinj hs ht heq
    refine Subtype.ext ?_
    exact mul_right_cancel₀ (ne_of_gt hbapos) (add_left_cancel h2)
  have hκrange : Set.range κ ⊆ γ.trace := by
    rintro x ⟨s, rfl⟩
    rw [hκ s]
    exact ⟨_, rfl⟩
  have hκball : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → κ t ∈ Metric.ball p ε := by
    intro t ht
    rw [hκ t, Metric.mem_ball, dist_eq_norm]
    exact hIoo _ ⟨by nlinarith [ht.1, hbapos], by nlinarith [ht.2, hbapos]⟩
  have h01 : (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ≠
      (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := by simp
  have hκ0eq : κ ⟨0, by norm_num⟩ = γ.γ a := by
    rw [hκ]
    congr 1
    simp
  have hκ1eq : κ ⟨1, by norm_num⟩ = γ.γ b := by
    rw [hκ]
    congr 1
    ring
  have hκ0 : κ ⟨0, by norm_num⟩ ∈ Metric.sphere p ε := by
    rw [hκ0eq, Metric.mem_sphere, dist_eq_norm]
    exact hspa
  have hκ1 : κ ⟨1, by norm_num⟩ ∈ Metric.sphere p ε := by
    rw [hκ1eq, Metric.mem_sphere, dist_eq_norm]
    exact hspb
  -- the arc is the component of `z` in the trace inside the ball
  have hBsubF : γ.γ '' Set.Ioo a b ⊆ γ.trace ∩ Metric.ball p ε := by
    rintro x ⟨t, ht, rfl⟩
    exact ⟨⟨t, rfl⟩, by rw [Metric.mem_ball, dist_eq_norm]; exact hIoo t ht⟩
  have hBsubC : γ.γ '' Set.Ioo a b ⊆ connectedComponentIn (γ.trace ∩ Metric.ball p ε) z :=
    (isPreconnected_Ioo.image γ.γ γ.cont.continuousOn).subset_connectedComponentIn
      (show z ∈ γ.γ '' Set.Ioo a b from ⟨θ, ⟨haθ, hθb⟩, hθ⟩) hBsubF
  have hCsub : connectedComponentIn (γ.trace ∩ Metric.ball p ε) z ⊆
      γ.γ '' Set.Icc a b ∪ γ.γ '' Set.Icc b (a + 2 * Real.pi) := by
    intro y hy
    have hyF := connectedComponentIn_subset (γ.trace ∩ Metric.ball p ε) z hy
    have hyT : y ∈ γ.γ '' Set.Icc a (a + 2 * Real.pi) := by
      rw [← htrace]
      exact hyF.1
    obtain ⟨t, ht, rfl⟩ := hyT
    rcases le_or_gt t b with h | h
    · exact Or.inl ⟨t, ⟨ht.1, h⟩, rfl⟩
    · exact Or.inr ⟨t, ⟨le_of_lt h, ht.2⟩, rfl⟩
  have huv_sub : γ.γ '' Set.Icc a b ∩ γ.γ '' Set.Icc b (a + 2 * Real.pi) ⊆ {γ.γ a, γ.γ b} := by
    rintro x ⟨⟨s, hsI, rfl⟩, ⟨t, htI, htx⟩⟩
    obtain ⟨k, hk⟩ := gamma_eq_imp_mod hs htx
    have h1 : (0 : ℝ) ≤ t - s := by linarith [htI.1, hsI.2]
    have h2 : t - s ≤ 2 * Real.pi := by linarith [htI.2, hsI.1]
    have hk0 : k = 0 ∨ k = 1 := by
      have hklo : (0 : ℝ) ≤ (k : ℝ) := by
        have h : (0 : ℝ) ≤ (k : ℝ) * (2 * Real.pi) := by rw [← hk]; exact h1
        nlinarith [Real.pi_pos]
      have hkhi : (k : ℝ) ≤ 1 := by
        have h : (k : ℝ) * (2 * Real.pi) ≤ 2 * Real.pi := by rw [← hk]; exact h2
        nlinarith [Real.pi_pos]
      have hk0i : (0 : ℤ) ≤ k := by exact_mod_cast hklo
      have hk1i : k ≤ 1 := by exact_mod_cast hkhi
      omega
    rcases hk0 with hk00 | hk11
    · have hts : t = s := by rw [hk00] at hk; simp at hk; linarith
      have hsb : s = b := le_antisymm hsI.2 (by linarith [hts, htI.1])
      right
      rw [hsb]
      simp
    · have hts : t = s + 2 * Real.pi := by rw [hk11] at hk; simp at hk; linarith
      have hsa : s = a := by linarith [hts, htI.2, hsI.1]
      left
      rw [hsa]
  have hC_disj : connectedComponentIn (γ.trace ∩ Metric.ball p ε) z ∩
      (γ.γ '' Set.Icc a b ∩ γ.γ '' Set.Icc b (a + 2 * Real.pi)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hyC, hyuv⟩
    have hyball : ‖y - p‖ < ε := by
      have h := (connectedComponentIn_subset (γ.trace ∩ Metric.ball p ε) z hyC).2
      rwa [Metric.mem_ball, dist_eq_norm] at h
    rcases huv_sub hyuv with h | h
    · rw [h, hspa] at hyball
      exact absurd hyball (lt_irrefl ε)
    · rw [h, hspb] at hyball
      exact absurd hyball (lt_irrefl ε)
  have hCsubB : connectedComponentIn (γ.trace ∩ Metric.ball p ε) z ⊆ γ.γ '' Set.Ioo a b := by
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
        (isPreconnected_connectedComponentIn (x := z) (F := γ.trace ∩ Metric.ball p ε))
        (γ.γ '' Set.Icc a b) (γ.γ '' Set.Icc b (a + 2 * Real.pi))
        (isCompact_Icc.image γ.cont).isClosed (isCompact_Icc.image γ.cont).isClosed
        hCsub hC_disj) with hcu | hcv
    · intro y hy
      obtain ⟨t, ht, rfl⟩ := hcu hy
      have hyball : ‖γ.γ t - p‖ < ε := by
        have h := (connectedComponentIn_subset (γ.trace ∩ Metric.ball p ε) z hy).2
        rwa [Metric.mem_ball, dist_eq_norm] at h
      have ht' : t ∈ Set.Ioo a b := by
        rw [Set.mem_Ioo]
        refine ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩
        · intro h
          rw [← h, hspa] at hyball
          exact absurd hyball (lt_irrefl ε)
        · intro h
          rw [h, hspb] at hyball
          exact absurd hyball (lt_irrefl ε)
      exact ⟨t, ht', rfl⟩
    · exfalso
      have hzC : z ∈ connectedComponentIn (γ.trace ∩ Metric.ball p ε) z := mem_connectedComponentIn hz
      obtain ⟨t, ht, htz⟩ := hcv hzC
      have heq : γ.γ t = γ.γ θ := by rw [htz, hθ]
      obtain ⟨k, hk⟩ := gamma_eq_imp_mod hs heq
      have h1 : 0 < t - θ := by linarith [ht.1, hθb]
      have h2 : t - θ < 2 * Real.pi := by linarith [ht.2, haθ]
      have hk1 : (0 : ℤ) < k := by
        have hkpos : (0 : ℝ) < (k : ℝ) := by nlinarith [hk, h1, Real.pi_pos]
        exact_mod_cast hkpos
      have hk2 : k < 1 := by
        have hklt : (k : ℝ) < 1 := by nlinarith [hk, h2, Real.pi_pos]
        exact_mod_cast hklt
      omega
  refine ⟨κ, hκinj, hκrange, hκball, h01, hκ0, hκ1, ?_⟩
  have hB : κ '' {t : Set.Icc (0 : ℝ) 1 | (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1} = γ.γ '' Set.Ioo a b := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨a + (s : ℝ) * (b - a),
        ⟨by nlinarith [hs.1, hbapos], by nlinarith [hs.2, hbapos]⟩, (hκ s).symm⟩
    · rintro ⟨t, ht, rfl⟩
      have hs0 : 0 < (t - a) / (b - a) := div_pos (sub_pos.mpr ht.1) hbapos
      have hs1 : (t - a) / (b - a) < 1 := by
        rw [div_lt_one hbapos]
        linarith [ht.2]
      refine ⟨⟨(t - a) / (b - a), le_of_lt hs0, le_of_lt hs1⟩, ⟨hs0, hs1⟩, ?_⟩
      rw [hκ]
      congr 1
      rw [div_mul_cancel₀ _ (ne_of_gt hbapos)]
      ring
  rw [hB]
  exact Set.Subset.antisymm hCsubB hBsubC

end Work.SphereJordan
