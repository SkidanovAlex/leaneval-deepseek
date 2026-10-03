import Mathlib

namespace Work.Horn

/-- The extension of an Abel/Fatou coordinate `Φ` (defined on `V`) to a set `B` which is
eventually captured by `V`: for `z ∈ B` one writes `Φ'(z) = Φ (g^[n] z) - n` where `n` is an
integer with `g^[n] z ∈ V`.  Well-definedness uses the invariance of `V` under `g` (so that the
Abel equation can be iterated along the tail of the orbit). -/
noncomputable def abelSpread (g Φ : ℂ → ℂ) (B V : Set ℂ)
    (h : ∀ z ∈ B, ∃ n : ℕ, (∀ k ≤ n, g^[k] z ∈ B) ∧ g^[n] z ∈ V) : ℂ → ℂ := by
  classical
  exact fun z =>
    if hz : z ∈ B then Φ (g^[Classical.choose (h z hz)] z)
      - ((Classical.choose (h z hz) : ℕ) : ℂ) else 0

/-- An Abel coordinate `Φ` on an invariant open set `V` extends holomorphically to any open set
`B ⊇ V` every point of which is eventually mapped into `V` (with intermediate iterates in `B`),
and the extension still satisfies the Abel equation `Φ' (g z) = Φ' z + 1` on `B`. -/
theorem abel_extension_to_spread {g : ℂ → ℂ} {B V : Set ℂ} {Φ : ℂ → ℂ}
    (hBopen : IsOpen B) (hgB : DifferentiableOn ℂ g B)
    (hVopen : IsOpen V) (hVsub : V ⊆ B) (hVmap : Set.MapsTo g V V)
    (hΦ : DifferentiableOn ℂ Φ V) (habel : ∀ z ∈ V, Φ (g z) = Φ z + 1)
    (henter : ∀ z ∈ B, ∃ n : ℕ, (∀ k ≤ n, g^[k] z ∈ B) ∧ g^[n] z ∈ V) :
    ∃ Φ' : ℂ → ℂ, DifferentiableOn ℂ Φ' B ∧ (∀ z ∈ B, Φ' (g z) = Φ' z + 1) ∧
      Set.EqOn Φ' Φ V := by
  classical
  -- `V` is invariant under all iterates of `g`.
  have hViter : ∀ (w : ℂ), w ∈ V → ∀ k : ℕ, g^[k] w ∈ V := by
    intro w hw k
    induction k with
    | zero => simpa using hw
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hVmap ih
  -- Iterated Abel equation along the orbit of a point of `V`.
  have habelIter : ∀ (w : ℂ), w ∈ V → ∀ k : ℕ, Φ (g^[k] w) = Φ w + (k : ℂ) := by
    intro w hw k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply', habel (g^[k] w) (hViter w hw k), ih]
        push_cast
        ring
  -- Any two "entry indices" give the same value `Φ (g^[n] z) - n`.
  have hcompare : ∀ (z : ℂ) (n m : ℕ), g^[n] z ∈ V → g^[m] z ∈ V →
      Φ (g^[n] z) - (n : ℂ) = Φ (g^[m] z) - (m : ℂ) := by
    intro z n m hn hm
    rcases le_total m n with hmn | hnm
    · have hn_eq : n = (n - m) + m := (Nat.sub_add_cancel hmn).symm
      have key : g^[n] z = g^[n - m] (g^[m] z) := by
        conv_lhs => rw [hn_eq, Function.iterate_add_apply]
      rw [key, habelIter (g^[m] z) hm (n - m)]
      have hcast : ((n - m : ℕ) : ℂ) = (n : ℂ) - (m : ℂ) := Nat.cast_sub hmn
      rw [hcast]; ring
    · have hm_eq : m = (m - n) + n := (Nat.sub_add_cancel hnm).symm
      have key : g^[m] z = g^[m - n] (g^[n] z) := by
        conv_lhs => rw [hm_eq, Function.iterate_add_apply]
      rw [key, habelIter (g^[n] z) hn (m - n)]
      have hcast : ((m - n : ℕ) : ℂ) = (m : ℂ) - (n : ℂ) := Nat.cast_sub hnm
      rw [hcast]; ring
  -- Value formula for the constructed extension.
  have hΦ'val : ∀ (z : ℂ) (hz : z ∈ B) (n : ℕ), g^[n] z ∈ V →
      abelSpread g Φ B V henter z = Φ (g^[n] z) - (n : ℂ) := by
    intro z hz n hn
    simp only [abelSpread]
    rw [dite_eq_left hz]
    exact hcompare z (Classical.choose (henter z hz)) n
      (Classical.choose_spec (henter z hz)).2 hn
  -- Holomorphy: near any `z0 ∈ B` the extension coincides with `z ↦ Φ (g^[n0] z) - n0`.
  have hdiffOn : DifferentiableOn ℂ (abelSpread g Φ B V henter) B := by
    intro z0 hz0
    set n0 : ℕ := Classical.choose (henter z0 hz0) with hn0
    have hspec : (∀ k ≤ n0, g^[k] z0 ∈ B) ∧ g^[n0] z0 ∈ V := by
      rw [hn0]; exact Classical.choose_spec (henter z0 hz0)
    have hdiff_iter : ∀ k, k ≤ n0 → DifferentiableAt ℂ (g^[k]) z0 := by
      intro k
      induction k with
      | zero => intro _; simpa using (differentiableAt_id (𝕜 := ℂ) (x := z0))
      | succ k ih =>
          intro hk
          rw [Function.iterate_succ']
          exact (hgB.differentiableAt
            (hBopen.mem_nhds (hspec.1 k (Nat.le_of_succ_le hk)))).comp z0
            (ih (Nat.le_of_succ_le hk))
    have hcont_iter : ∀ k, k ≤ n0 → ContinuousAt (g^[k]) z0 :=
      fun k hk => (hdiff_iter k hk).continuousAt
    have hEv : ∀ᶠ z in nhds z0, (∀ k ≤ n0, g^[k] z ∈ B) ∧ g^[n0] z ∈ V := by
      have h1 : ∀ᶠ z in nhds z0, ∀ k ∈ Finset.range (n0 + 1), g^[k] z ∈ B := by
        rw [Filter.eventually_all_finset]
        intro k hk
        have hk' : k ≤ n0 := by
          simp only [Finset.mem_range] at hk; omega
        exact (hcont_iter k hk').preimage_mem_nhds (hBopen.mem_nhds (hspec.1 k hk'))
      have h2 : ∀ᶠ z in nhds z0, g^[n0] z ∈ V :=
        (hcont_iter n0 le_rfl).preimage_mem_nhds (hVopen.mem_nhds hspec.2)
      filter_upwards [h1, h2] with z hz1 hz2
      exact ⟨fun k hk => hz1 k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)), hz2⟩
    have hcongr : (abelSpread g Φ B V henter) =ᶠ[nhds z0]
        (fun z => Φ (g^[n0] z) - (n0 : ℂ)) := by
      filter_upwards [hEv] with z hz
      exact hΦ'val z (hz.1 0 (Nat.zero_le n0)) n0 hz.2
    have hd : DifferentiableAt ℂ (fun z => Φ (g^[n0] z) - (n0 : ℂ)) z0 := by
      have h1 : DifferentiableAt ℂ (fun z => Φ (g^[n0] z)) z0 :=
        (hΦ.differentiableAt (hVopen.mem_nhds hspec.2)).comp z0 (hdiff_iter n0 le_rfl)
      exact h1.sub (differentiableAt_const (n0 : ℂ))
    exact ((hcongr.differentiableAt_iff).2 hd).differentiableWithinAt
  -- The Abel equation on `B`.
  have hequiv : ∀ z ∈ B,
      abelSpread g Φ B V henter (g z) = abelSpread g Φ B V henter z + 1 := by
    intro z hz
    set n : ℕ := Classical.choose (henter z hz) with hn
    have hspecz : (∀ k ≤ n, g^[k] z ∈ B) ∧ g^[n] z ∈ V := by
      rw [hn]; exact Classical.choose_spec (henter z hz)
    have hhv : g^[n] z ∈ V := hspecz.2
    have hgzB : g z ∈ B := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · have hzV : z ∈ V := by simpa [h0] using hspecz.2
        exact hVsub (hVmap hzV)
      · have h1 : g^[1] z ∈ B := hspecz.1 1 hpos
        simpa using h1
    have hzval : abelSpread g Φ B V henter z = Φ (g^[n] z) - (n : ℂ) := hΦ'val z hz n hhv
    have hgz_val : abelSpread g Φ B V henter (g z) = Φ (g^[n] (g z)) - (n : ℂ) := by
      refine hΦ'val (g z) hgzB n ?_
      have hstep : g^[n] (g z) = g (g^[n] z) := by
        rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
      rw [hstep]; exact hVmap hhv
    rw [hzval, hgz_val]
    have hstep : g^[n] (g z) = g (g^[n] z) := by
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
    rw [hstep, habel (g^[n] z) hhv]
    ring
  -- Agreement with `Φ` on `V` (take the entry index `0`).
  have hEq : Set.EqOn (abelSpread g Φ B V henter) Φ V := by
    intro z hzV
    have hzB : z ∈ B := hVsub hzV
    have h := hΦ'val z hzB 0 (by simpa using hzV)
    simpa [Function.iterate_zero_apply] using h
  exact ⟨abelSpread g Φ B V henter, hdiffOn, hequiv, hEq⟩

end Work.Horn
