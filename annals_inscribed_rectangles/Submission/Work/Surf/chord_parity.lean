import Mathlib
import Submission.Work.Drive.boxParity
import Submission.Work.Drive.Surf.Model
import Submission.Work.Surf.chordFamily
import Submission.Work.Surf.chordFamily_parity
import Submission.Work.Surf.tau_face_parity
import Submission.Work.Surf.ncard_chordMeet_straightChord
import Submission.Work.Surf.chordMeet_straight_odd
import Submission.Work.Surf.signChangeAt_of_hasDerivAt
import Submission.Work.Surf.chordMeet_finite

namespace Work.Surf

/-- **The base case of the mod-2 intersection form of `ℝP²`: two chords in general position cross an
odd number of times.**

A *chord* is a curve `a` with `Work.Drive.IsChord a` (`a (t+1) = -a t`, `‖a t‖ ≤ 1`, `a 0` on the unit
circle); `Work.Drive.chordMeet a b = {(s,t) ∈ (0,1)² : a s = b t}` is the count of crossings of the two
1-chains, which is the mod-2 intersection number of the two essential loops of `ℝP²` that the chords
represent (see `Submission/Work/Surf/CHORD_PARITY_STATUS.md`).

Hypotheses: `a`, `b` are smooth chords (`hasm`, `hbsm` — `boxParity` needs `C^∞`), `hint` excludes
crossings with a parameter on the boundary of the square, and `htrans` is the transversality of the
*straightening family* `τ ↦ chordHom a (a 0) τ` (from the chord `a` to the diameter through `a 0`)
against `b`: at every interior crossing of a family member with `b`, the two tangents are independent.

Proof recipe (all ingredients are proved; see `Submission/Work/Surf/chord_parity_partial.lean`, which
already contains steps 1–3):
1. `Work.Surf.chordFamily_parity a b ha hb hasm hbsm hint htrans` (rewrite `htrans` into the form it
   expects with `Work.Surf.deriv_chordHom ha.contDiff`) gives the three `Submission.Drive.ParityProp`
   hypotheses for `F := Work.Surf.chordDiff a b` on the cube `[0,1]³` (coordinates `(τ,s,t)`) and the
   freeness of the four faces `x 1 ∈ {0,1}`, `x 2 ∈ {0,1}`.
2. `Work.Surf.even_ncard_tauFaces` gives `Even (N₀ + N₁)`, `N₀`, `N₁` the numbers of zeros on the
   faces `x 0 = 0` resp. `x 0 = 1`.
3. Identify `N₀ = (chordMeet a b).ncard` and `N₁ = (chordMeet (straightChord (a 0)) b).ncard` with
   `Set.ncard_congr` and the map `x ↦ (x 1, x 2)` (the `Work.Surf.tauFace` definition and the proofs
   are in `chord_parity_partial.lean`).
4. `Odd N₁`: apply `Work.Surf.chordMeet_straight_odd` to the chord `b` with `w = a 0` (so the count
   `Odd (chordMeet b (straightChord (a 0))).ncard`; transfer through the swap bijection).
   Its `hint` (no boundary crossings) follows from the *freeness of the side faces* obtained in step 1
   (apply it at `x = (1, t, s)`: if `s ∈ {0,1}` or `t ∈ {0,1}` then
   `cos (π t) • a 0 ≠ b s`), and the bound `‖b s‖ < 1` for `t ∈ (0,1)` from
   `Real.strictAntiOn_cos` (`|cos (π t)| < 1` for `t ∈ (0,1)`, the argument used inside
   `Work.Surf.chordDiff_ne_zero_of_tface`).
   Its `htrans` follows from `htrans` at `τ = 1` (after `Work.Surf.deriv_chordHom`), i.e.
   `det2 (a 0) (deriv b s) ≠ 0`, together with `Work.Surf.deriv_straightChord` and the skew-symmetry
   `Work.Drive.det2_skew`.
   (Alternative: `Work.Surf.ncard_chordMeet_straightChord` plus the parity of the zeros of
   `t ↦ det2 (b t) (a 0)`: finitely many — they correspond to the `τ = 1` face, finite by step 1 —
   each a sign change by `htrans` at `τ = 1` and `Work.Surf.signChangeAt_of_hasDerivAt`, with
   `det2 (b 1) (a 0) = -det2 (b 0) (a 0) ≠ 0`; then
   `Work.Drive.odd_ncard_zeros_of_opposite_signs`.)
5. `Even (N₀ + N₁)` and `Odd N₁` give `Odd (chordMeet a b).ncard`. -/
theorem chord_parity (a b : ℝ → EuclideanSpace ℝ (Fin 2))
    (ha : Work.Drive.IsChord a) (hb : Work.Drive.IsChord b)
    (hasm : ContDiff ℝ Work.Drive.Ctop a) (hbsm : ContDiff ℝ Work.Drive.Ctop b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0 : ℝ) 1 ∧ t ∈ Set.Ioo (0 : ℝ) 1)
    (htrans : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ s t : ℝ, s ∈ Set.Ioo (0 : ℝ) 1 → t ∈ Set.Ioo (0 : ℝ) 1 →
      (1 - τ) • a s + τ • (Real.cos (Real.pi * s) • a 0) = b t →
      Work.Drive.det2 ((1 - τ) • deriv a s - τ • ((Real.pi * Real.sin (Real.pi * s)) • a 0))
        (deriv b t) ≠ 0) :
    Odd (Work.Drive.chordMeet a b).ncard := by
  classical
  -- **Step 1**: the box-parity hypotheses for the difference map of the straightening family.
  have htrans' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ s t : ℝ, s ∈ Set.Ioo (0 : ℝ) 1 →
      t ∈ Set.Ioo (0 : ℝ) 1 → Work.Surf.chordHom a (a 0) τ s = b t →
      Work.Drive.det2 (deriv (fun u : ℝ => Work.Surf.chordHom a (a 0) τ u) s) (deriv b t) ≠ 0 := by
    intro τ hτ s t hs ht hch
    rw [Work.Surf.deriv_chordHom ha.contDiff τ s]
    exact htrans τ hτ s t hs ht hch
  obtain ⟨hFsm, hreg, hface, hside⟩ :=
    Work.Surf.chordFamily_parity a b ha hb hasm hbsm hint htrans'
  -- **Step 2**: the two `τ`-faces carry an even total number of zeros.
  have heven := Work.Surf.even_ncard_tauFaces (Work.Surf.chordDiff a b) hFsm hreg hface hside
  -- **Step 3a**: the `τ = 0` face is `chordMeet a b`.
  have hN0 : ({x ∈ Submission.Drive.unitBox 2 | x 0 = 0 ∧ Work.Surf.chordDiff a b x = 0} :
      Set (Work.Drive.Amb 2)).ncard = (Work.Drive.chordMeet a b).ncard := by
    refine Set.ncard_congr (fun x _ => (x 1, x 2)) ?_ ?_ ?_
    · rintro x ⟨hx, hx0, hxz⟩
      obtain ⟨hs, ht⟩ := Work.Surf.chord_side_of_zero ha hb hint hx hxz
      refine ⟨hs, ht, ?_⟩
      have h := hxz
      rw [Work.Surf.chordDiff_eq] at h
      rw [hx0, Work.Surf.chordHom_zero] at h
      exact sub_eq_zero.mp h
    · intro x y hx hy hxy
      obtain ⟨hxb, hx0, hxz⟩ := hx
      obtain ⟨hyb, hy0, hyz⟩ := hy
      have h1 : x 1 = y 1 := by simpa using congrArg Prod.fst hxy
      have h2 : x 2 = y 2 := by simpa using congrArg Prod.snd hxy
      exact PiLp.ext (by intro i; fin_cases i <;> simp [hx0, hy0, h1, h2])
    · rintro ⟨s, t⟩ ⟨hs, ht, heq⟩
      refine ⟨WithLp.toLp 2 (![0, s, t] : Fin 3 → ℝ), ?_, rfl⟩
      refine ⟨?_, rfl, ?_⟩
      · intro i; fin_cases i
        · norm_num
        · exact ⟨le_of_lt hs.1, le_of_lt hs.2⟩
        · exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      · rw [Work.Surf.chordDiff_apply]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons]
        simp [heq]
  -- **Step 3b**: the `τ = 1` face is `chordMeet b (straightChord (a 0))`.
  have hN1 : ({x ∈ Submission.Drive.unitBox 2 | x 0 = 1 ∧ Work.Surf.chordDiff a b x = 0} :
      Set (Work.Drive.Amb 2)).ncard
      = (Work.Drive.chordMeet b (Work.Drive.straightChord (a 0))).ncard := by
    refine Set.ncard_congr (fun x _ => (x 2, x 1)) ?_ ?_ ?_
    · rintro x ⟨hx, hx1, hxz⟩
      obtain ⟨hs, ht⟩ := Work.Surf.chord_side_of_zero ha hb hint hx hxz
      refine ⟨ht, hs, ?_⟩
      have h := hxz
      rw [Work.Surf.chordDiff_eq] at h
      rw [hx1, Work.Surf.chordHom_one] at h
      exact (sub_eq_zero.mp h).symm
    · intro x y hx hy hxy
      obtain ⟨hxb, hx1, hxz⟩ := hx
      obtain ⟨hyb, hy1, hyz⟩ := hy
      have h1 : x 1 = y 1 := by simpa using congrArg Prod.snd hxy
      have h2 : x 2 = y 2 := by simpa using congrArg Prod.fst hxy
      exact PiLp.ext (by intro i; fin_cases i <;> simp [hx1, hy1, h1, h2])
    · rintro ⟨u, v⟩ ⟨hu, hv, heq⟩
      refine ⟨WithLp.toLp 2 (![1, v, u] : Fin 3 → ℝ), ?_, rfl⟩
      refine ⟨?_, rfl, ?_⟩
      · intro i; fin_cases i
        · norm_num
        · exact ⟨le_of_lt hv.1, le_of_lt hv.2⟩
        · exact ⟨le_of_lt hu.1, le_of_lt hu.2⟩
      · rw [Work.Surf.chordDiff_apply]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons]
        simp [heq, Work.Drive.straightChord]
  -- **Step 4a**: the `hint` hypothesis for the chord `b` against the diameter through `a 0`.
  have hint2 : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 →
      b s = Work.Drive.straightChord (a 0) t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖b s‖ < 1 := by
    intro s t hs ht heq
    -- the point `x = (1, t, s)` of the cube; its image under `chordDiff` is `cos (π t) • a 0 - b s`
    have hbox : (WithLp.toLp 2 (![1, t, s] : Fin 3 → ℝ) : Work.Drive.Amb 2) ∈
        Submission.Drive.unitBox 2 := by
      intro i; fin_cases i
      · norm_num
      · exact ⟨ht.1, ht.2⟩
      · exact ⟨hs.1, hs.2⟩
    have hzero : Work.Surf.chordDiff a b (WithLp.toLp 2 (![1, t, s] : Fin 3 → ℝ) :
        Work.Drive.Amb 2) = 0 := by
      rw [Work.Surf.chordDiff_apply]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons]
      simp [heq, Work.Drive.straightChord]
    have hc1 : (WithLp.toLp 2 (![1, t, s] : Fin 3 → ℝ) : Work.Drive.Amb 2) 1 = t := by simp
    have hc2 : (WithLp.toLp 2 (![1, t, s] : Fin 3 → ℝ) : Work.Drive.Amb 2) 2 = s := by simp
    have htne0 : t ≠ 0 := by
      intro h; exact hside _ hbox (by rw [hc1]; exact Or.inl h) hzero
    have htne1 : t ≠ 1 := by
      intro h; exact hside _ hbox (by rw [hc1]; exact Or.inr (Or.inl h)) hzero
    have hsne0 : s ≠ 0 := by
      intro h; exact hside _ hbox (by rw [hc2]; exact Or.inr (Or.inr (Or.inl h))) hzero
    have hsne1 : s ≠ 1 := by
      intro h; exact hside _ hbox (by rw [hc2]; exact Or.inr (Or.inr (Or.inr h))) hzero
    refine ⟨⟨lt_of_le_of_ne hs.1 (Ne.symm hsne0), lt_of_le_of_ne hs.2 hsne1⟩,
      ⟨lt_of_le_of_ne ht.1 (Ne.symm htne0), lt_of_le_of_ne ht.2 htne1⟩, ?_⟩
    -- on the diameter: `b s = cos (π t) • a 0`, and `|cos (π t)| < 1` for `t ∈ (0,1)`
    have hbs : b s = Real.cos (Real.pi * t) • a 0 := heq
    have hn : ‖b s‖ = |Real.cos (Real.pi * t)| := by
      rw [hbs, norm_smul, Real.norm_eq_abs, ha.start, mul_one]
    rw [hn]
    have hpi0 : 0 < Real.pi * t := by
      have := lt_of_le_of_ne ht.1 (Ne.symm htne0); nlinarith [Real.pi_pos]
    have hpipi : Real.pi * t < Real.pi := by
      have := lt_of_le_of_ne ht.2 htne1; nlinarith [Real.pi_pos]
    have h1 := Real.strictAntiOn_cos (show (0:ℝ) ∈ Set.Icc 0 Real.pi from ⟨le_refl _, Real.pi_pos.le⟩)
      (show Real.pi * t ∈ Set.Icc 0 Real.pi from ⟨hpi0.le, hpipi.le⟩) hpi0
    have h2 := Real.strictAntiOn_cos (show Real.pi * t ∈ Set.Icc 0 Real.pi from ⟨hpi0.le, hpipi.le⟩)
      (show Real.pi ∈ Set.Icc 0 Real.pi from ⟨Real.pi_pos.le, le_refl _⟩) hpipi
    rw [Real.cos_zero] at h1
    rw [Real.cos_pi] at h2
    exact abs_lt.mpr ⟨h2, h1⟩
  -- **Step 4b**: the transversality hypothesis for the chord `b` against the diameter, from `htrans`
  -- at `τ = 1`.
  have htrans2 : ∀ s t : ℝ, s ∈ Set.Ioo (0:ℝ) 1 → t ∈ Set.Ioo (0:ℝ) 1 →
      b s = Work.Drive.straightChord (a 0) t →
      Work.Drive.det2 (deriv b s) (deriv (Work.Drive.straightChord (a 0)) t) ≠ 0 := by
    intro s t hs ht hbs
    have hch : ((1 : ℝ) - 1) • a t + (1 : ℝ) • (Real.cos (Real.pi * t) • a 0) = b s := by
      simp [hbs, Work.Drive.straightChord]
    have htr := htrans 1 (by norm_num) t s ht hs hch
    simp only [sub_self, zero_smul, one_smul, zero_sub] at htr
    rw [Work.Surf.deriv_straightChord]
    have hkey : Work.Drive.det2 (deriv b s) ((-(Real.pi * Real.sin (Real.pi * t))) • a 0)
        = - Work.Drive.det2 (-((Real.pi * Real.sin (Real.pi * t)) • a 0)) (deriv b s) := by
      have h1 : Work.Drive.det2 (deriv b s) ((-(Real.pi * Real.sin (Real.pi * t))) • a 0)
          = (-(Real.pi * Real.sin (Real.pi * t))) * Work.Drive.det2 (deriv b s) (a 0) :=
        Work.Drive.det2_smul_right _ _ _
      have h2 : Work.Drive.det2 (-((Real.pi * Real.sin (Real.pi * t)) • a 0)) (deriv b s)
          = (Real.pi * Real.sin (Real.pi * t)) * Work.Drive.det2 (deriv b s) (a 0) := by
        rw [← neg_smul, Work.Drive.det2_smul_left, Work.Drive.det2_skew (a 0) (deriv b s)]
        ring
      rw [h1, h2]
      ring
    rw [hkey]
    exact neg_ne_zero.mpr htr
  have hodd1 : Odd (Work.Drive.chordMeet b (Work.Drive.straightChord (a 0))).ncard :=
    Work.Surf.chordMeet_straight_odd hb ha.start hint2 htrans2
  -- **Step 5**: combine.
  have heven' : Even ((Work.Drive.chordMeet a b).ncard +
      (Work.Drive.chordMeet b (Work.Drive.straightChord (a 0))).ncard) := by
    rw [← hN0, ← hN1]
    exact heven
  have hnot : ¬ Even (Work.Drive.chordMeet a b).ncard := fun h =>
    (Nat.not_even_iff_odd.mpr hodd1) ((Nat.even_add.mp heven').mp h)
  exact Nat.not_even_iff_odd.mp hnot

end Work.Surf
