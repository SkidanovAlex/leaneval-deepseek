import Mathlib
import Submission.Work.TMC16Core.Assembly.RegWin
import Submission.Work.TMC16Core.Assembly.local_patch
import Submission.Work.TMC16Core.Assembly.decay_final_arith
import Submission.Work.TMC16Core.Assembly.res_zone_arith
import Submission.Work.TMC16Core.Assembly.res_final_arith

namespace Work.TMC16Core.Assembly

open Work.TMC16Core

/-- **One decay step.**  Let `[a,b]` be a zone of `(γ,g)`-regular sites, with `g = (Q-1)/40` and
windows of exactly `Q-1` sites, and let `u` be a formal solution which is a priori bounded by
`C·(1+3Q)` on the enlarged zone `[a-Q, b+Q]`.  If `k ∈ [a,b]` is at distance at least
`d - (Q-1)/20 - 4` from both endpoints, then the Poisson iteration `local_patch` at the optimal
number of steps `n` (supplied by `res_final_arith`) gives `‖u k‖ ≤ exp (-(L/2)·d)`.

The hypothesis `hboxw` records that the zone is inside a regularity box
`[(Q-1)/20+3, 95(Q-1)/100-3]` (which has width `9(Q-1)/10 - 6`); it is used only to bound the
depth `dZ = min(k-a,b-k)+1` by `Q-1 = 40g`. -/
private lemma res_decay_step {α lam θ γ L : ℝ} {E : ℂ} {u : ℤ → ℂ} {C : ℝ} {Q : ℕ} {d : ℕ}
    {k a b : ℤ}
    (hγ : 0 < γ) (hγ7 : 7 * L / 10 ≤ γ) (hL : 0 < L) (hC0 : 0 ≤ C)
    (hQ : 300 ≤ Q) (hd5 : (Q : ℝ) ≤ 5 * (d : ℝ))
    (hsol : IsFormalSol α lam θ E u)
    (ha : a ≤ k) (hb : k ≤ b)
    (hboxw : (b : ℝ) - (a : ℝ) ≤ 9 * ((((Q - 1 : ℕ) : ℝ))) / 10 - 6)
    (hreg : ∀ y : ℤ, a ≤ y → y ≤ b →
      RegWin α lam θ E γ ((((Q - 1 : ℕ) : ℝ)) / 40) (Q - 1) y)
    (hM : ∀ z : ℤ, a - (Q : ℤ) ≤ z → z ≤ b + (Q : ℤ) →
      ‖u z‖ ≤ C * (1 + 3 * (Q : ℝ)))
    (hdz : (d : ℝ) - ((((Q - 1 : ℕ) : ℝ)) / 20 + 4) ≤
      ((min (k - a) (b - k) : ℤ) : ℝ) + 1)
    (habs : C * (1 + 3 * (Q : ℝ)) *
        Real.exp (5 * (7 * L / 10) + 41 * (7 * L / 10 + Real.log 2)) ≤
      Real.exp (L / 40 * (d : ℝ))) :
    ‖u k‖ ≤ Real.exp (-(L / 2) * (d : ℝ)) := by
  have hQ1 : 1 ≤ Q := by omega
  have hQQnn : (0 : ℝ) ≤ (((Q - 1 : ℕ) : ℝ)) := by positivity
  have hg1 : 1 ≤ ((((Q - 1 : ℕ) : ℝ)) / 40) := by
    have h : (40 : ℝ) ≤ (((Q - 1 : ℕ) : ℝ)) := by
      have h' : (40 : ℕ) ≤ Q - 1 := by omega
      exact_mod_cast h'
    linarith
  have hQsub : (((Q - 1 : ℕ) : ℤ)) = (Q : ℤ) - 1 := by
    rw [Nat.cast_sub hQ1]; simp
  have hM' : ∀ z : ℤ, a - (((Q - 1 : ℕ) : ℤ)) - 1 ≤ z →
      z ≤ b + (((Q - 1 : ℕ) : ℤ)) + 1 → ‖u z‖ ≤ C * (1 + 3 * (Q : ℝ)) := by
    intro z h1 h2
    have h1' : a - (Q : ℤ) ≤ z := by rw [hQsub] at h1; omega
    have h2' : z ≤ b + (Q : ℤ) := by rw [hQsub] at h2; omega
    exact hM z h1' h2'
  have hreg' : ∀ y : ℤ, a ≤ y → y ≤ b → ∃ K : ℕ, K ≤ Q - 1 ∧
      RegWin α lam θ E γ ((((Q - 1 : ℕ) : ℝ)) / 40) K y :=
    fun y h1 h2 => ⟨Q - 1, le_rfl, hreg y h1 h2⟩
  have hpatch := local_patch (α := α) (lam := lam) (θ := θ) (E := E) (u := u)
    (a := a) (b := b) (γ := γ) (g := ((((Q - 1 : ℕ) : ℝ)) / 40))
    (M := C * (1 + 3 * (Q : ℝ))) (D := Q - 1)
    hsol hγ hg1 (by positivity) hM' hreg'
  have hdZ0 : (0 : ℝ) ≤ ((min (k - a) (b - k) : ℤ) : ℝ) + 1 := by
    have h : (0 : ℤ) ≤ min (k - a) (b - k) := le_min (by omega) (by omega)
    have h'' : (0 : ℝ) ≤ ((min (k - a) (b - k) : ℤ) : ℝ) := by exact_mod_cast h
    linarith
  have h40 : ((min (k - a) (b - k) : ℤ) : ℝ) + 1 ≤ 40 * ((((Q - 1 : ℕ) : ℝ)) / 40) := by
    have h2 : (2 * min (k - a) (b - k) : ℤ) ≤ b - a := by
      have h2a : min (k - a) (b - k) ≤ k - a := min_le_left _ _
      have h2b : min (k - a) (b - k) ≤ b - k := min_le_right _ _
      omega
    have hcast : ((2 * min (k - a) (b - k) : ℤ) : ℝ) ≤ ((b - a : ℤ) : ℝ) := by
      exact_mod_cast h2
    rw [Int.cast_mul, Int.cast_ofNat, Int.cast_sub] at hcast
    linarith
  obtain ⟨N, ⟨hN1, hN2⟩, hfin⟩ := res_final_arith (γ := γ) (L := L) (C := C) (Q := Q)
    (d := d) (dZ := ((min (k - a) (b - k) : ℤ) : ℝ) + 1) (g := ((((Q - 1 : ℕ) : ℝ)) / 40))
    hL hγ7 hC0 hQ hd5 hdZ0 hg1 h40 hdz habs
  exact le_trans (hpatch N k ha hb) hfin

theorem res_decay_pos {α lam γ L : ℝ} {q : ℕ → ℕ}
    (hγ : 0 < γ) (hL : 0 < L) (hγ7 : 7 * L / 10 ≤ γ) (hγL : γ ≤ L)
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q) :
    ∀ {θ : ℝ} {E : ℂ} {u : ℤ → ℂ} {C : ℝ},
      Work.TMC16Core.IsFormalSol α lam θ E u → u 0 = 1 →
      0 ≤ C → (∀ k : ℤ, ‖u k‖ ≤ C * (1 + |(k : ℝ)|)) →
      ∃ N : ℕ, ∀ n ≥ N,
        (∀ y : ℤ, ((((q n - 1 : ℕ) : ℝ))) / 20 + 3 ≤ (y : ℝ) →
          (y : ℝ) ≤ 95 * ((((q n - 1 : ℕ) : ℝ))) / 100 - 3 →
          Work.TMC16Core.Assembly.RegWin α lam θ E γ ((((q n - 1 : ℕ) : ℝ)) / 40) (q n - 1) y) →
        (∀ y : ℤ, (q n : ℝ) + ((((q n - 1 : ℕ) : ℝ))) / 20 + 3 ≤ (y : ℝ) →
          (y : ℝ) ≤ (q n : ℝ) + 95 * ((((q n - 1 : ℕ) : ℝ))) / 100 - 3 →
          Work.TMC16Core.Assembly.RegWin α lam θ E γ ((((q n - 1 : ℕ) : ℝ)) / 40) (q n - 1) y) →
        ∀ k : ℤ, (q n : ℝ) / 5 ≤ (k : ℝ) → (k : ℝ) ≤ 9 * (q n : ℝ) / 5 →
          ∀ d : ℕ, q n ≤ 5 * d → (∀ ℓ : ℤ, (d : ℤ) ≤ |k - ℓ * (q n : ℤ)|) →
          ‖u k‖ ≤ Real.exp (-(L / 2) * (d : ℝ)) := by
  intro θ E u C hsol hu0 hC0 hgrowth
  obtain ⟨Nf, hf⟩ := decay_final_arith hL hC0 hmono
  refine ⟨max Nf 1000, ?_⟩
  intro n hn hbox0 hbox1 k hk1 hk2 d hd5 hsep
  have hn1000 : 1000 ≤ n := le_trans (le_max_right _ _) hn
  have hnNf : Nf ≤ n := le_trans (le_max_left _ _) hn
  have hqn1000 : 1000 ≤ q n := le_trans hn1000 (StrictMono.id_le hmono n)
  have hQnd : (q n : ℝ) ≤ 5 * (d : ℝ) := by exact_mod_cast hd5
  have habs := hf n hnNf d hd5
  have hs0 : (d : ℝ) ≤ |(k : ℝ)| := by
    have h := hsep 0
    have h' : ((d : ℤ) : ℝ) ≤ ((|k - (0 : ℤ) * (q n : ℤ)| : ℤ) : ℝ) := by exact_mod_cast h
    simpa using h'
  have hs1 : (d : ℝ) ≤ |(k : ℝ) - (q n : ℝ)| := by
    have h := hsep 1
    have h' : ((d : ℤ) : ℝ) ≤ ((|k - (1 : ℤ) * (q n : ℤ)| : ℤ) : ℝ) := by exact_mod_cast h
    simpa using h'
  have hs2 : (d : ℝ) ≤ |(k : ℝ) - 2 * (q n : ℝ)| := by
    have h := hsep 2
    have h' : ((d : ℤ) : ℝ) ≤ ((|k - (2 : ℤ) * (q n : ℤ)| : ℤ) : ℝ) := by exact_mod_cast h
    simpa using h'
  have hq5 : (q n : ℝ) / 5 ≤ (d : ℝ) := by linarith
  have hQQle : (((q n - 1 : ℕ) : ℝ)) ≤ (q n : ℝ) := by
    exact_mod_cast Nat.sub_le (q n) 1
  have hQQnn : (0 : ℝ) ≤ (((q n - 1 : ℕ) : ℝ)) := by positivity
  by_cases hkQ : k ≤ (q n : ℤ)
  · -- ## case A: `k ≤ q n`, the zone sits at `0`
    have hkQr : (k : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hkQ
    have hkpos : (0 : ℝ) ≤ (k : ℝ) := by linarith
    have hA1 : (d : ℝ) ≤ (k : ℝ) := by
      have h : |(k : ℝ)| = (k : ℝ) := abs_of_nonneg hkpos
      linarith [hs0, h]
    have hA2 : (d : ℝ) ≤ (q n : ℝ) - (k : ℝ) := by
      have h : |(k : ℝ) - (q n : ℝ)| = (q n : ℝ) - (k : ℝ) := by
        rw [abs_of_nonpos (show (k : ℝ) - (q n : ℝ) ≤ 0 by linarith)]
        ring
      linarith [hs1, h]
    have hm2 : 5 * (k : ℝ) ≤ 4 * (q n : ℝ) := by linarith
    obtain ⟨a, b, hboxa, hboxb, ham, hmb, hdz⟩ :=
      res_zone_arith (Q := q n) (m := k) (d := d) (by omega) hk1 hm2 hA1 hA2
    have hboxw : (b : ℝ) - (a : ℝ) ≤ 9 * ((((q n - 1 : ℕ) : ℝ))) / 10 - 6 := by linarith
    have hbq : (b : ℝ) ≤ (q n : ℝ) := by linarith [hboxb, hQQnn, hQQle]
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := by linarith [hboxa, hQQnn]
    have hreg : ∀ y : ℤ, a ≤ y → y ≤ b →
        RegWin α lam θ E γ ((((q n - 1 : ℕ) : ℝ)) / 40) (q n - 1) y := by
      intro y hy1 hy2
      refine hbox0 y ?_ ?_
      · have h : (a : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
        linarith
      · have h : (y : ℝ) ≤ (b : ℝ) := by exact_mod_cast hy2
        linarith
    have hM : ∀ z : ℤ, a - (q n : ℤ) ≤ z → z ≤ b + (q n : ℤ) →
        ‖u z‖ ≤ C * (1 + 3 * (q n : ℝ)) := by
      intro z h1 h2
      have hz1 : -(3 * (q n : ℝ)) ≤ (z : ℝ) := by
        have h : ((a - (q n : ℤ) : ℤ) : ℝ) ≤ (z : ℝ) := by exact_mod_cast h1
        push_cast at h
        linarith
      have hz2 : (z : ℝ) ≤ 3 * (q n : ℝ) := by
        have h : (z : ℝ) ≤ ((b + (q n : ℤ) : ℤ) : ℝ) := by exact_mod_cast h2
        push_cast at h
        linarith
      have hz3 : |(z : ℝ)| ≤ 3 * (q n : ℝ) := abs_le.mpr ⟨hz1, hz2⟩
      calc ‖u z‖ ≤ C * (1 + |(z : ℝ)|) := hgrowth z
        _ ≤ C * (1 + 3 * (q n : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ hC0
            linarith
    exact res_decay_step (k := k) (a := a) (b := b) (Q := q n) (d := d)
      hγ hγ7 hL hC0 (by omega) hQnd hsol ham hmb hboxw hreg hM hdz habs
  · -- ## case B: `q n < k`, the zone sits at `q n`
    have hkQlt : (q n : ℤ) < k := lt_of_not_ge hkQ
    have hkQr : (q n : ℝ) < (k : ℝ) := by exact_mod_cast hkQlt
    set m : ℤ := k - (q n : ℤ) with hm
    have hmcast : (m : ℝ) = (k : ℝ) - (q n : ℝ) := by rw [hm]; push_cast; ring
    have habs1 : |(k : ℝ) - (q n : ℝ)| = (k : ℝ) - (q n : ℝ) :=
      abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) - (q n : ℝ) by linarith)
    have habs2 : |(k : ℝ) - 2 * (q n : ℝ)| = 2 * (q n : ℝ) - (k : ℝ) := by
      rw [abs_of_nonpos (show (k : ℝ) - 2 * (q n : ℝ) ≤ 0 by linarith)]
      ring
    have hm1 : (q n : ℝ) / 5 ≤ (m : ℝ) := by
      have h1 : (d : ℝ) ≤ (k : ℝ) - (q n : ℝ) := by linarith [hs1, habs1]
      rw [hmcast]; linarith
    have hm2 : 5 * (m : ℝ) ≤ 4 * (q n : ℝ) := by
      rw [hmcast]; linarith
    have hd1 : (d : ℝ) ≤ (m : ℝ) := by
      have h1 : (d : ℝ) ≤ (k : ℝ) - (q n : ℝ) := by linarith [hs1, habs1]
      rw [hmcast]; linarith
    have hd2 : (d : ℝ) ≤ (q n : ℝ) - (m : ℝ) := by
      have h1 : (d : ℝ) ≤ 2 * (q n : ℝ) - (k : ℝ) := by linarith [hs2, habs2]
      rw [hmcast]; linarith
    obtain ⟨a, b, hboxa, hboxb, ham, hmb, hdz⟩ :=
      res_zone_arith (Q := q n) (m := m) (d := d) (by omega) hm1 hm2 hd1 hd2
    have hboxw : ((b + (q n : ℤ) : ℤ) : ℝ) - ((a + (q n : ℤ) : ℤ) : ℝ) ≤
        9 * ((((q n - 1 : ℕ) : ℝ))) / 10 - 6 := by
      push_cast
      linarith
    have hbq : (b : ℝ) ≤ (q n : ℝ) := by linarith [hboxb, hQQnn, hQQle]
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := by linarith [hboxa, hQQnn]
    have hkA : a + (q n : ℤ) ≤ k := by omega
    have hkB : k ≤ b + (q n : ℤ) := by omega
    have hdz' : (d : ℝ) - ((((q n - 1 : ℕ) : ℝ)) / 20 + 4) ≤
        ((min (k - (a + (q n : ℤ))) ((b + (q n : ℤ)) - k) : ℤ) : ℝ) + 1 := by
      have h1 : k - (a + (q n : ℤ)) = m - a := by rw [hm]; ring
      have h2 : (b + (q n : ℤ)) - k = b - m := by rw [hm]; ring
      rw [h1, h2]
      exact hdz
    have hreg : ∀ y : ℤ, a + (q n : ℤ) ≤ y → y ≤ b + (q n : ℤ) →
        RegWin α lam θ E γ ((((q n - 1 : ℕ) : ℝ)) / 40) (q n - 1) y := by
      intro y hy1 hy2
      refine hbox1 y ?_ ?_
      · have h : ((a + (q n : ℤ) : ℤ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
        push_cast at h
        linarith
      · have h : (y : ℝ) ≤ ((b + (q n : ℤ) : ℤ) : ℝ) := by exact_mod_cast hy2
        push_cast at h
        linarith
    have hM : ∀ z : ℤ, a + (q n : ℤ) - (q n : ℤ) ≤ z →
        z ≤ b + (q n : ℤ) + (q n : ℤ) → ‖u z‖ ≤ C * (1 + 3 * (q n : ℝ)) := by
      intro z h1 h2
      have h1' : a ≤ z := by omega
      have h2' : z ≤ b + 2 * (q n : ℤ) := by omega
      have hz1 : -(3 * (q n : ℝ)) ≤ (z : ℝ) := by
        have h : (a : ℝ) ≤ (z : ℝ) := by exact_mod_cast h1'
        linarith
      have hz2 : (z : ℝ) ≤ 3 * (q n : ℝ) := by
        have h : (z : ℝ) ≤ ((b + 2 * (q n : ℤ) : ℤ) : ℝ) := by exact_mod_cast h2'
        push_cast at h
        linarith
      have hz3 : |(z : ℝ)| ≤ 3 * (q n : ℝ) := abs_le.mpr ⟨hz1, hz2⟩
      calc ‖u z‖ ≤ C * (1 + |(z : ℝ)|) := hgrowth z
        _ ≤ C * (1 + 3 * (q n : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ hC0
            linarith
    exact res_decay_step (k := k) (a := a + (q n : ℤ)) (b := b + (q n : ℤ))
      (Q := q n) (d := d) hγ hγ7 hL hC0 (by omega) hQnd hsol hkA hkB hboxw
      hreg hM hdz' habs

end Work.TMC16Core.Assembly
