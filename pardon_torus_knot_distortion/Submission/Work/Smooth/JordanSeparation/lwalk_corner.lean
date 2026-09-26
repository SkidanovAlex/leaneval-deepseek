import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_peel
import Submission.Work.Smooth.JordanSeparation.lwalk_region

/-!
# The corner step of the peel

`cellCl_close`: the closed cell is the closure of the open cell, hence a closed cell inside the
bounded side has its closure in `U`; `corner_edge_*`: the two edges of the walk at the lex-max
vertex are the two sides of the corner cell.  These are the inputs of `joinNat_replace` in the
corner step of the peel.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-! ### The closed cell is the closure of the open cell -/

theorem closure_unitCell_subset_cellCl {c : ℝ} {p : ℤ × ℤ} :
    closure (unitCell c p) ⊆ cellCl c p :=
  closure_minimal (cell_subset_cellCl c p) (isClosed_cellCl c p)

theorem cellCl_subset_closure_unitCell {c : ℝ} (hc : 0 < c) {p : ℤ × ℤ} :
    cellCl c p ⊆ closure (unitCell c p) := by
  intro z hz
  rw [mem_cellCl] at hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  rw [Metric.mem_closure_iff]
  intro ε hε
  -- the centre of the cell
  set w : ℂ := (((p.1 : ℝ) + 1 / 2) * c : ℝ) + ((((p.2 : ℝ) + 1 / 2) * c : ℝ)) * Complex.I
    with hwdef
  have hwmem : w ∈ unitCell c p := by
    rw [mem_cell, hwdef]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> nlinarith [hc]
  have hwre : w.re = ((p.1 : ℝ) + 1 / 2) * c := by simp [hwdef]
  have hwim : w.im = ((p.2 : ℝ) + 1 / 2) * c := by simp [hwdef]
  -- work with a small positive parameter
  set t : ℝ := min (1 / 2) (ε / (2 * (dist w z + 1))) with ht
  have htpos : 0 < t := by
    rw [ht]
    refine lt_min (by norm_num) ?_
    have : (0:ℝ) < 2 * (dist w z + 1) := by positivity
    positivity
  have htlt1 : t < 1 := by
    rw [ht]; exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have htle : t ≤ ε / (2 * (dist w z + 1)) := by rw [ht]; exact min_le_right _ _
  set z' : ℂ := (1 - t) • z + t • w with hz'def
  refine ⟨z', ?_, ?_⟩
  · -- `z'` is in the open cell
    rw [mem_cell]
    have hz're : z'.re = (1 - t) * z.re + t * w.re := by
      simp only [hz'def, Complex.add_re, Complex.smul_re]
      ring
    have hz'im : z'.im = (1 - t) * z.im + t * w.im := by
      simp only [hz'def, Complex.add_im, Complex.smul_im]
      ring
    have ht0 : (0:ℝ) < t := htpos
    have ht1 : t ≤ 1 := le_of_lt htlt1
    have hpos1 : (0:ℝ) ≤ 1 - t := by linarith
    have hzre1 : (p.1 : ℝ) * c < z'.re := by
      rw [hz're, hwre]
      have ha : (1 - t) * ((p.1 : ℝ) * c) ≤ (1 - t) * z.re :=
        mul_le_mul_of_nonneg_left h1 hpos1
      have hb : t * ((p.1 : ℝ) * c) < t * (((p.1 : ℝ) + 1 / 2) * c) := by nlinarith [htpos, hc]
      nlinarith [ha, hb]
    have hzre2 : z'.re < ((p.1 : ℝ) + 1) * c := by
      rw [hz're, hwre]
      have ha : (1 - t) * z.re ≤ (1 - t) * (((p.1 : ℝ) + 1) * c) :=
        mul_le_mul_of_nonneg_left h2 hpos1
      have hb : t * (((p.1 : ℝ) + 1 / 2) * c) < t * (((p.1 : ℝ) + 1) * c) := by
        nlinarith [htpos, hc]
      nlinarith [ha, hb]
    have hzim1 : (p.2 : ℝ) * c < z'.im := by
      rw [hz'im, hwim]
      have ha : (1 - t) * ((p.2 : ℝ) * c) ≤ (1 - t) * z.im :=
        mul_le_mul_of_nonneg_left h3 hpos1
      have hb : t * ((p.2 : ℝ) * c) < t * (((p.2 : ℝ) + 1 / 2) * c) := by nlinarith [htpos, hc]
      nlinarith [ha, hb]
    have hzim2 : z'.im < ((p.2 : ℝ) + 1) * c := by
      rw [hz'im, hwim]
      have ha : (1 - t) * z.im ≤ (1 - t) * (((p.2 : ℝ) + 1) * c) :=
        mul_le_mul_of_nonneg_left h4 hpos1
      have hb : t * (((p.2 : ℝ) + 1 / 2) * c) < t * (((p.2 : ℝ) + 1) * c) := by
        nlinarith [htpos, hc]
      nlinarith [ha, hb]
    exact ⟨hzre1, hzre2, hzim1, hzim2⟩
  · -- and it is close to `z`
    have hsub : z' - z = t • (w - z) := by
      rw [hz'def, smul_sub, sub_smul, one_smul]
      abel
    rw [dist_comm, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have hb : t * dist w z ≤ (ε / (2 * (dist w z + 1))) * dist w z :=
      mul_le_mul_of_nonneg_right htle (dist_nonneg : (0:ℝ) ≤ dist w z)
    have hb2 : (ε / (2 * (dist w z + 1))) * dist w z ≤ ε / 2 := by
      rw [div_mul_eq_mul_div]
      have h1 : ε * dist w z ≤ ε * (dist w z + 1) := by
        nlinarith [hε, (dist_nonneg : (0:ℝ) ≤ dist w z)]
      have h2 : (0:ℝ) < 2 * (dist w z + 1) := by positivity
      calc ε * dist w z / (2 * (dist w z + 1))
          ≤ ε * (dist w z + 1) / (2 * (dist w z + 1)) :=
            div_le_div_of_nonneg_right h1 (le_of_lt h2)
        _ = ε / 2 := by field_simp
    have hwd : dist w z = ‖w - z‖ := dist_eq_norm w z
    rw [hwd] at hb hb2
    linarith

/-- **A closed cell contained in the bounded side has its closure in `U`.** -/
theorem cellCl_subset_U {U : Set ℂ} (hUo : IsOpen U)
    (hpre : IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' Uᶜ ∪ {OnePoint.infty}))
    {W : LWalk} (hW : W.IsSimple) (hn : 4 ≤ W.n) (hval : ∀ t, W.path t ∈ U)
    (S : Work.Smooth.Jordan.PlaneSeparation W.toPlaneCurve) {q : ℤ × ℤ}
    (hq : unitCell W.c q ⊆ S.V) : cellCl W.c q ⊆ U := by
  have h1 : closure (unitCell W.c q) ⊆ closure S.V := closure_mono hq
  have h2 : cellCl W.c q ⊆ closure S.V :=
    (cellCl_subset_closure_unitCell W.cpos).trans h1
  exact h2.trans (W.closure_boundedSide_subset hUo hpre hW hn hval S)


/-! ### `edgeU` is the lifted segment -/

/-- The lifted `k`-th edge of the walk *is* the lifted straight segment between its endpoints, as
computed by `segIn` for any convex `B ⊆ U` containing them.  (Both sides are `Path.liftU` of
`Path.segment` between the same points; the endpoint-membership proofs live in `Prop`.) -/
theorem edgeU_eq_segIn {U B : Set ℂ} {hB : Convex ℝ B} {hBU : B ⊆ U} {W : LWalk}
    {hval : ∀ t, W.path t ∈ U} {k : ℕ} (hk : k < W.n)
    (ha : W.pt k ∈ B) (hb : W.pt (k + 1) ∈ B) :
    W.edgeU hval k hk = segIn hB hBU ha hb :=
  Path.ext (funext fun _ => Subtype.ext rfl)


/-- The clamped lifted edge, for `k < W.n`, is the lifted segment: both sides are cast to the same
endpoints `⟨W.pt k, _⟩`, `⟨W.pt (k+1), _⟩` so that no composite of endpoint equalities appears in
the statement (which is what made the elaboration expensive). -/
theorem edgeUNat_eq_segIn {U B : Set ℂ} {hB : Convex ℝ B} {hBU : B ⊆ U} {W : LWalk}
    {hval : ∀ t, W.path t ∈ U} {k : ℕ} (hk : k < W.n)
    (ha : W.pt k ∈ B) (hb : W.pt (k + 1) ∈ B) :
    (W.edgeUNat hval k).cast
      ((W.ptMin_eq_ptU hval k (le_of_lt hk)).symm)
      ((W.ptMin_eq_ptU hval (k + 1) (Nat.succ_le_of_lt hk)).symm)
      = segIn hB hBU ha hb := by
  apply Path.ext
  funext t
  rw [LWalk.edgeUNat, dif_pos hk]
  rw [path_cast_apply, path_cast_apply, edgeU_eq_segIn hk ha hb]


/-! ### The corner data at the lex-max vertex -/

/-- **The two neighbours of the lex-max vertex.**  If `p = W.v k` is lexicographically maximal
among the vertices of `W` and `1 ≤ k`, `k+1 ≤ W.n`, then the two neighbours of `p` in the walk are
`p - (1,0)` and `p - (0,1)` (in some order), and they are distinct.  This is the data the corner
move consumes: which two lifted segments sit at `p`, and that no degenerate case occurs. -/
theorem corner_data {W : LWalk} {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n) {p : ℤ × ℤ}
    (hp : W.v k = p)
    (hlex : ∀ j, j ≤ W.n → ((W.v j).1 < p.1) ∨ ((W.v j).1 = p.1 ∧ (W.v j).2 ≤ p.2))
    (hW : W.IsSimple) (hn : 2 < W.n) :
    (W.v (k - 1) = p - (1, 0) ∨ W.v (k - 1) = p - (0, 1)) ∧
    (W.v (k + 1) = p - (1, 0) ∨ W.v (k + 1) = p - (0, 1)) ∧
    W.v (k - 1) ≠ W.v (k + 1) := by
  have hd1 : W.v (k - 1) = p - (1, 0) ∨ W.v (k - 1) = p - (0, 1) := by
    have hstep : GridStep (W.v (k - 1)) p := by
      have h := W.step (k - 1) (by omega)
      rwa [show k - 1 + 1 = k from by omega, hp] at h
    exact LWalk.eq_sub_of_gridStep_le_left hstep (hlex (k - 1) (by omega))
  have hd2 : W.v (k + 1) = p - (1, 0) ∨ W.v (k + 1) = p - (0, 1) := by
    have hstep : GridStep (W.v (k + 1)) p := by
      have h := gridStep_symm (W.step k (by omega))
      rwa [hp] at h
    exact LWalk.eq_sub_of_gridStep_le_left hstep (hlex (k + 1) hk2)
  have hne : W.v (k - 1) ≠ W.v (k + 1) := by
    refine hW (k - 1) (k + 1) (by omega) hk2 ?_
    intro hc
    have h1 : k - 1 = 0 := congrArg Prod.fst hc
    have h2 : k + 1 = W.n := congrArg Prod.snd hc
    omega
  exact ⟨hd1, hd2, hne⟩


/-! ### The corner homotopy, in the form the peel consumes -/

/-- **The corner step.**  The two consecutive lifted edges `j`, `j+1` of the walk — the pair that
meets at the vertex `W.pt (j+1)` — are homotopic *in `↥U`* to the two-step path through any other
point `s ∈ B` (for the peel, the opposite corner `W.c • gpt (W.v (j+1) - (1,1))` of the corner
cell).

The statement deliberately uses the *unclamped* `W.edgeU` and the index shape `j`, `j+1`: the
endpoints of `W.edgeU` are definitionally `⟨W.pt ·, _⟩` (proof irrelevance), so they are *the same
types* as the endpoints of `segIn`, and no endpoint cast appears at all. -/
theorem corner_step {U B : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U} {j : ℕ}
    (hj1 : j < W.n) (hj2 : j + 1 < W.n) {hB : Convex ℝ B} {hBU : B ⊆ U}
    (hBne : B.Nonempty)
    {s : ℂ} (ha : W.pt j ∈ B) (hp : W.pt (j + 1) ∈ B) (hb : W.pt ((j + 1) + 1) ∈ B)
    (hs : s ∈ B) :
    Path.Homotopic ((W.edgeU hval j hj1).trans (W.edgeU hval (j + 1) hj2))
      ((segIn hB hBU ha hs).trans (segIn hB hBU hs hb)) := by
  rw [edgeU_eq_segIn hj1 ha hp, edgeU_eq_segIn hj2 hp hb]
  exact corner_homotopic hB hBne hBU ha hp hb hs



/-- **The clamped composite is the cast of the unclamped composite.** -/
theorem edgeUNat_trans_eq {U B : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U} {j : ℕ}
    (hj1 : j < W.n) (hj2 : j + 1 < W.n) {hB : Convex ℝ B} {hBU : B ⊆ U}
    (ha : W.pt j ∈ B) (hp : W.pt (j + 1) ∈ B) (hb : W.pt ((j + 1) + 1) ∈ B) :
    (W.edgeUNat hval j).trans (W.edgeUNat hval (j + 1))
      = ((W.edgeU hval j hj1).trans (W.edgeU hval (j + 1) hj2)).cast
          (W.ptMin_eq_ptU hval j (le_of_lt hj1))
          (W.ptMin_eq_ptU hval ((j + 1) + 1) (Nat.succ_le_of_lt hj2)) := by
  have e1 : W.ptMin hval j = W.ptU hval j (le_of_lt hj1) := W.ptMin_eq_ptU hval j (le_of_lt hj1)
  have e2 : W.ptMin hval (j + 1) = W.ptU hval (j + 1) (Nat.succ_le_of_lt hj1) :=
    W.ptMin_eq_ptU hval (j + 1) (Nat.succ_le_of_lt hj1)
  have e2' : W.ptMin hval (j + 1) = W.ptU hval (j + 1) (le_of_lt hj2) :=
    W.ptMin_eq_ptU hval (j + 1) (le_of_lt hj2)
  have e3 : W.ptMin hval ((j + 1) + 1) = W.ptU hval ((j + 1) + 1) (Nat.succ_le_of_lt hj2) :=
    W.ptMin_eq_ptU hval ((j + 1) + 1) (Nat.succ_le_of_lt hj2)
  have hcast1 : (W.edgeUNat hval j).cast e1.symm e2.symm = W.edgeU hval j hj1 := by
    have hA : (W.edgeUNat hval j).cast e1.symm e2.symm = segIn hB hBU ha hp :=
      edgeUNat_eq_segIn (hval := hval) hj1 ha hp
    have hB' : W.edgeU hval j hj1 = segIn hB hBU ha hp :=
      edgeU_eq_segIn (hval := hval) hj1 ha hp
    rw [hA, hB']
  have hcast2 : (W.edgeUNat hval (j + 1)).cast e2'.symm e3.symm = W.edgeU hval (j + 1) hj2 := by
    have hA : (W.edgeUNat hval (j + 1)).cast e2'.symm e3.symm = segIn hB hBU hp hb :=
      edgeUNat_eq_segIn (hval := hval) hj2 hp hb
    have hB' : W.edgeU hval (j + 1) hj2 = segIn hB hBU hp hb :=
      edgeU_eq_segIn (hval := hval) hj2 hp hb
    rw [hA, hB']
  have hFj : W.edgeUNat hval j = (W.edgeU hval j hj1).cast e1 e2 := by
    have h := congrArg (fun γ => γ.cast e1 e2) hcast1
    rw [Path.cast_cast, Path.cast_self] at h
    exact h
  have hFj1 : W.edgeUNat hval (j + 1) = (W.edgeU hval (j + 1) hj2).cast e2' e3 := by
    have h := congrArg (fun γ => γ.cast e2' e3) hcast2
    rw [Path.cast_cast, Path.cast_self] at h
    exact h
  rw [hFj, hFj1, ← cast_trans_general (W.edgeU hval j hj1) (W.edgeU hval (j + 1) hj2) e1 e2 e3]

end

end Work.Smooth.JordanSeparation
