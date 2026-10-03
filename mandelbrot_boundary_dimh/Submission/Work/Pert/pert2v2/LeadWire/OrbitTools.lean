import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# `Work.Pert.pert2v2.LeadWire.OrbitTools` — the chart decomposition of an `R`-orbit (S16)

`orbit_chart_decomp_orb` is `Work.Pert.pert2v2.orbit_chart_decomp` with its two global
hypotheses replaced by what is actually used:

* the per-step real-part drop `Re R^[j+1] w ≤ Re R^[j] w - Re (1/α) + e` only ALONG THE ORBIT
  (the original asks for `|Re (R y) - Re y + Re (1/α)| ≤ e` on all of `DR`, which is not available
  for the low chart near the real axis, where `d.E - id` is unbounded);
* the left bound `x₀ - Re (1/α) + Bl ≤ Re w'` only AT the target point `w'` (the original asks it on
  all of `Dφ`, which is FALSE for `Dφ = DphiP … (Qm Ξabs α)`: the gate contains points of arbitrarily
  negative real part at large `|Im|`);

and with the extra conclusion `Bl - e - 1 < n` (the final shift dominates the left reduction).
The proof is the original one.
-/

namespace Work.Pert.pert2v2.LeadWire

open MandelDim Set Metric Filter Topology

theorem orbit_chart_decomp_orb {R : ℂ → ℂ} {DR Ulow Uhigh : Set ℂ} {α w w' : ℂ} {m m₀ : ℕ}
    {x₀ R1 e Bl : ℝ}
    (hDR : DR = ⋃ n : ℤ, (fun u : ℂ => u + (n : ℂ)) '' (Ulow ∪ Uhigh))
    (hwin : Ulow ∪ Uhigh ⊆ {z : ℂ | |z.re - x₀| < R1}) (hR1 : R1 ≤ 1)
    (hstepOrb : ∀ j < m, (R^[j+1] w).re ≤ (R^[j] w).re - (1 / α).re + e)
    (hA : (m₀ : ℝ) + e + 4 ≤ (1 / α).re)
    (hBl : (m₀ : ℝ) + e + 2 ≤ Bl)
    (hw'left : x₀ - (1 / α).re + Bl ≤ w'.re)
    (hm : 1 ≤ m) (hw0 : w ∈ Ulow ∪ Uhigh) (hiter : ∀ j < m, R^[j] w ∈ DR)
    (hpi : MandelDim.piExp (R^[m] w) = MandelDim.piExp w') :
    ∃ (n : ℕ) (x : ℕ → ℂ) (k : ℕ → ℤ) (b : ℕ → Bool),
      w' = R^[m] w + (n : ℂ) ∧ k 0 = 0 ∧
      (∀ j < m, R^[j] w = x j + (k j : ℂ)) ∧
      (∀ j < m, (b j = true → x j ∈ Ulow) ∧ (b j = false → x j ∈ Uhigh)) ∧
      (∀ j, j + 1 < m → k (j+1) ≤ k j) ∧
      (∀ j, 1 ≤ j → j ≤ m - 1 → k j ≤ 0) ∧
      (∀ j, j + 1 < m → (m₀ : ℤ) ≤ k j - k (j+1)) ∧
      ((-k (m-1)).toNat : ℕ) ≤ n ∧
      (m₀ : ℤ) ≤ k (m-1) + (n : ℤ) ∧
      Bl - e - 1 < (n : ℝ) := by
  classical
  have hex : ∀ j : ℕ, j < m →
      ∃ q : ℂ × ℤ, q.1 ∈ Ulow ∪ Uhigh ∧ R^[j] w = q.1 + ((q.2 : ℤ) : ℂ) := by
    intro j hj
    have hmem : R^[j] w ∈ ⋃ n : ℤ, (fun u : ℂ => u + (n : ℂ)) '' (Ulow ∪ Uhigh) := by
      rw [← hDR]; exact hiter j hj
    rw [Set.mem_iUnion] at hmem
    obtain ⟨n, u, hu, hux⟩ := hmem
    exact ⟨(u, n), hu, hux.symm⟩
  let p : ℕ → ℂ × ℤ := fun j =>
    if j = 0 then (w, 0) else if h : j < m then Classical.choose (hex j h) else (0, 0)
  have hp0 : p 0 = (w, 0) := by simp [p]
  have hpspec : ∀ j (hj : j < m),
      (p j).1 ∈ Ulow ∪ Uhigh ∧ R^[j] w = (p j).1 + ((p j).2 : ℂ) := by
    intro j hj
    by_cases h0 : j = 0
    · subst h0
      rw [hp0]
      exact ⟨hw0, by simp⟩
    · simp only [p, if_neg h0, dif_pos hj]
      exact Classical.choose_spec (hex j hj)
  let x : ℕ → ℂ := fun j => (p j).1
  let k : ℕ → ℤ := fun j => (p j).2
  have hkk : k 0 = 0 := by simp [k, p]
  have hdec : ∀ j (hj : j < m), R^[j] w = x j + (k j : ℂ) := fun j hj => (hpspec j hj).2
  have hside : ∀ j (hj : j < m), x j ∈ Ulow ∪ Uhigh := fun j hj => (hpspec j hj).1
  have hxabs : ∀ j (hj : j < m), |(x j).re - x₀| < R1 := fun j hj => hwin (hside j hj)
  have hRre : ∀ j (hj : j < m), (R^[j] w).re = (x j).re + (k j : ℝ) := by
    intro j hj
    rw [hdec j hj, Complex.add_re]
    simp
  have hklow : ∀ j (hj : j < m), (R^[j] w).re - x₀ - 1 < (k j : ℝ) := by
    intro j hj
    have h := (abs_lt.mp (hxabs j hj)).2
    have h1 : (x j).re - x₀ < 1 := lt_of_lt_of_le h hR1
    have h2 := hRre j hj
    linarith
  have hkhigh : ∀ j (hj : j < m), (k j : ℝ) < (R^[j] w).re - x₀ + 1 := by
    intro j hj
    have h := (abs_lt.mp (hxabs j hj)).1
    have h1 : x₀ - 1 < (x j).re := by linarith
    have h2 := hRre j hj
    linarith
  have hstep : ∀ j (hj : j < m),
      (R^[j+1] w).re ≤ (R^[j] w).re - (1 / α).re + e := fun j hj => hstepOrb j hj
  have hlvl : ∀ j, j + 1 < m → (m₀ : ℤ) ≤ k j - k (j+1) := by
    intro j hj
    have hj1 : j < m := by omega
    have h1 := hklow j hj1
    have h2 := hkhigh (j+1) hj
    have hs := hstep j hj1
    have hreal : (m₀ : ℝ) + 2 < (k j : ℝ) - (k (j+1) : ℝ) := by
      have hA' := hA
      linarith
    have h3 : (m₀ : ℤ) + 2 < k j - k (j+1) := by exact_mod_cast hreal
    omega
  have hanti : ∀ j, j + 1 < m → k (j+1) ≤ k j := by
    intro j hj
    have := hlvl j hj
    omega
  have hneg0 : ∀ j, j ≤ m - 1 → k j ≤ 0 := by
    intro j
    induction j with
    | zero => intro _; simp [hkk]
    | succ i ih =>
      intro hi
      have him : i + 1 < m := by omega
      have h1 := hlvl i him
      have h2 := ih (by omega)
      omega
  have hneg : ∀ j, 1 ≤ j → j ≤ m - 1 → k j ≤ 0 := fun j _ hj => hneg0 j hj
  obtain ⟨N, hN⟩ : ∃ N : ℤ, w' = R^[m] w + (N : ℂ) := by
    have hpi' := hpi
    simp only [MandelDim.piExp] at hpi'
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hpi'
    refine ⟨-n, ?_⟩
    have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      have h1 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero two_ne_zero h1) Complex.I_ne_zero
    have key : (2 * (Real.pi : ℂ) * Complex.I) * (R^[m] w)
        = (2 * (Real.pi : ℂ) * Complex.I) * (w' + (n : ℂ)) := by
      rw [hn]; ring
    have haux := mul_left_cancel₀ hc key
    rw [haux]; push_cast; ring
  have hNre : w'.re = (R^[m] w).re + (N : ℝ) := by
    rw [hN, Complex.add_re]
    simp
  have hmlt : m - 1 < m := by omega
  have h1 := hklow (m-1) hmlt
  have h2 : (R^[m] w).re ≤ (R^[m-1] w).re - (1 / α).re + e := by
    have h := hstep (m-1) hmlt
    rwa [show m - 1 + 1 = m by omega] at h
  have h3 : x₀ - (1 / α).re + Bl ≤ w'.re := hw'left
  have hkeyR : Bl - e - 1 < (k (m-1) : ℝ) + (N : ℝ) := by linarith
  have hkey : (m₀ : ℤ) + 1 < k (m-1) + N := by
    have hreal : (m₀ : ℝ) + 1 < (k (m-1) : ℝ) + (N : ℝ) := by linarith
    exact_mod_cast hreal
  have hkml : k (m-1) ≤ 0 := hneg0 (m-1) (by omega)
  have hNnn : 0 ≤ N := by omega
  have hle : -k (m-1) ≤ N := by omega
  have hnmono : ((-k (m-1)).toNat : ℕ) ≤ N.toNat := Int.toNat_le_toNat hle
  have hNcast : ((N.toNat : ℕ) : ℤ) = N := Int.toNat_of_nonneg hNnn
  have hmemlast : (m₀ : ℤ) ≤ k (m-1) + ((N.toNat : ℕ) : ℤ) := by
    rw [hNcast]
    omega
  have hw'eq : w' = R^[m] w + ((N.toNat : ℕ) : ℂ) := by
    have h1 : ((N.toNat : ℕ) : ℂ) = (N : ℂ) := by exact_mod_cast hNcast
    rw [hN, ← h1]
  have hNbig : Bl - e - 1 < ((N.toNat : ℕ) : ℝ) := by
    have hkml' : (k (m-1) : ℝ) ≤ 0 := by exact_mod_cast hkml
    have h1 : ((N.toNat : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast hNcast
    rw [h1]; linarith
  refine ⟨N.toNat, x, k, fun j => decide (x j ∈ Ulow), hw'eq, hkk, hdec, ?_, hanti, hneg, hlvl,
    hnmono, hmemlast, hNbig⟩
  intro j hj
  constructor
  · intro h
    exact of_decide_eq_true h
  · intro h
    exact (hside j hj).resolve_left (of_decide_eq_false h)

/-- Integer translates stay in a `T`-invariant set. -/
theorem mem_add_int_of_TInv {D : Set ℂ} (hD : MandelDim.IsTInvariant D) {u : ℂ} (hu : u ∈ D)
    (n : ℤ) : u + (n : ℂ) ∈ D := by
  induction n using Int.induction_on with
  | zero => simpa using hu
  | succ i ih =>
    have := (hD (u + (i : ℂ))).mp ih
    push_cast
    rw [← add_assoc]; exact this
  | pred i ih =>
    have h1 : u + ((-(i : ℤ) - 1 : ℤ) : ℂ) + 1 = u + ((-(i : ℤ) : ℤ) : ℂ) := by push_cast; ring
    have := (hD (u + ((-(i : ℤ) - 1 : ℤ) : ℂ))).mpr (by rw [h1]; exact ih)
    exact this

/-- **Iterates commute with integer translation** along an orbit inside a `T`-equivariance domain. -/
theorem iterate_sub_int {R : ℂ → ℂ} {DR : Set ℂ} (h : MandelDim.IsTEquivariantOn R DR)
    (hRn : ∀ (n : ℤ) (u : ℂ), u ∈ DR → R (u + (n : ℂ)) = R u + (n : ℂ))
    {w : ℂ} {m : ℕ} (hiter : ∀ j < m, R^[j] w ∈ DR) (k : ℤ) :
    ∀ j, j ≤ m → R^[j] (w - (k : ℂ)) = R^[j] w - (k : ℂ) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have hi' : i ≤ m := Nat.le_of_succ_le hi
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hi']
    have hmem := hiter i (Nat.lt_of_succ_le hi)
    have := hRn (-k) (R^[i] w) hmem
    have e1 : R^[i] w - (k : ℂ) = R^[i] w + ((-k : ℤ) : ℂ) := by push_cast; ring
    rw [e1, this]; push_cast; ring

/-- `piExp` is `1`-periodic under integer translation. -/
theorem piExp_sub_int (z : ℂ) (k : ℤ) : MandelDim.piExp (z - (k : ℂ)) = MandelDim.piExp z := by
  simp only [MandelDim.piExp]
  have h : 2 * (Real.pi : ℂ) * Complex.I * (z - (k : ℂ))
      = 2 * (Real.pi : ℂ) * Complex.I * z + (-k : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The forward ray.**  Along a ray `w, w+1, …, w+s` inside `Dφ`, the Abel relation gives
`φ (w + i) = f^[i] (φ w)`, and the points before the last are mapped into `Df`. -/
theorem phi_ray_forward {f φ : ℂ → ℂ} {Dφ Df : Set ℂ} {w : ℂ} {s : ℕ}
    (hAbel : ∀ z ∈ Dφ, z + 1 ∈ Dφ → φ z ∈ Df ∧ φ (z + 1) = f (φ z))
    (hray : ∀ i : ℕ, i ≤ s → w + (i : ℂ) ∈ Dφ) :
    ∀ i : ℕ, i ≤ s → φ (w + (i : ℂ)) = f^[i] (φ w) ∧ (i < s → f^[i] (φ w) ∈ Df) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨by simp, fun h0 => ?_⟩
    have h1 := hAbel w (by simpa using hray 0 (Nat.zero_le _)) (by simpa using hray 1 h0)
    simpa using h1.1
  | succ i ih =>
    intro hi
    have hi' : i ≤ s := Nat.le_of_succ_le hi
    obtain ⟨ih1, -⟩ := ih hi'
    have hA := hAbel (w + (i : ℂ)) (hray i hi') (by
      have := hray (i + 1) hi; push_cast at this ⊢; rw [add_assoc]; exact this)
    have hval : φ (w + ((i + 1 : ℕ) : ℂ)) = f^[i + 1] (φ w) := by
      have e : w + ((i + 1 : ℕ) : ℂ) = w + (i : ℂ) + 1 := by push_cast; ring
      rw [e, hA.2, ih1, Function.iterate_succ_apply']
    refine ⟨hval, fun hlt => ?_⟩
    have hB := hAbel (w + ((i + 1 : ℕ) : ℂ)) (hray (i + 1) hi) (by
      have := hray (i + 2) hlt; push_cast at this ⊢
      rw [show w + ((i : ℂ) + 1) + 1 = w + ((i : ℂ) + 2) by ring]; exact this)
    rw [← hval]; exact hB.1

/-- **Membership along an orbit extended to the left by a ray.** -/
theorem orbit_mem_right_extend {f φ : ℂ → ℂ} {Dφ Df : Set ℂ} {w : ℂ} {s N : ℕ}
    (hAbel : ∀ z ∈ Dφ, z + 1 ∈ Dφ → φ z ∈ Df ∧ φ (z + 1) = f (φ z))
    (hray : ∀ i : ℕ, i ≤ s → w + (i : ℂ) ∈ Dφ)
    (hmem : ∀ i : ℕ, i < N → f^[i] (φ (w + (s : ℂ))) ∈ Df) :
    ∀ i : ℕ, i < N + s → f^[i] (φ w) ∈ Df := by
  intro i hi
  have hr := phi_ray_forward hAbel hray
  by_cases his : i < s
  · exact (hr i his.le).2 his
  · push_neg at his
    have h1 : f^[i] (φ w) = f^[i - s] (f^[s] (φ w)) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel his]
    rw [h1, ← (hr s le_rfl).1]
    exact hmem (i - s) (by omega)

end Work.Pert.pert2v2.LeadWire
