/-
  Area C4aU: shared definitions and bookkeeping lemmas for the syntactic lemma
  `Work.WilC4aU.clusterFam_rexExist` (`Submission/Work/WilC4aU/clusterFam_rexExist.lean`).

  The ambient index type is the left-nested sum
  `BB7 k = (((((((Fin 1 ⊕ Fin k) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1`
  whose coordinates, in order, are `lam`, `c : Fin k`, `eps`, `x`, `u`, `y`, `y'`, `z`, `w`.
  Because it is left-nested, the trailing single coordinates are peeled off by repeated
  `RExpExistI.projLast`, and the block `c` (of `BB0 k = Fin 1 ⊕ Fin k`) by
  `RExpExistI.existsBlock`.

  `Body` is the conjunction whose projection is the set `Dset` of parameters `(lam, c, eps)`
  with `∃ x y y', 1 ≤ eps * x ∧ … `; the key content is `proj6_body_mem`, the bijection between
  the six slack witnesses `(x,u,y,y',z,w)` and the three "real" ones `(x,y,y')`.
-/
import Submission.Work.WilC0.Compl

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
noncomputable section
open Classical
open MvPolynomial

namespace Work.WilC4aU

open WilkiesDesign (rexp RExpExist)
open Work.WilC0

/-! ## 1. The index type and its coordinates -/

abbrev BB0 (k : ℕ) := Fin 1 ⊕ Fin k
abbrev BB1 (k : ℕ) := BB0 k ⊕ Fin 1
abbrev BB2 (k : ℕ) := BB1 k ⊕ Fin 1
abbrev BB3 (k : ℕ) := BB2 k ⊕ Fin 1
abbrev BB4 (k : ℕ) := BB3 k ⊕ Fin 1
abbrev BB5 (k : ℕ) := BB4 k ⊕ Fin 1
abbrev BB6 (k : ℕ) := BB5 k ⊕ Fin 1
abbrev BB7 (k : ℕ) := BB6 k ⊕ Fin 1

/-- The inclusion of the block `BB0 k` (the coordinates `lam`, `c`) into the ambient type. -/
def lift {k : ℕ} (x : BB0 k) : BB7 k :=
  Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl x))))))

/-- The `lam` coordinate. -/
def iLam (k : ℕ) : BB7 k := lift (Sum.inl (0 : Fin 1))
/-- The `c` coordinate. -/
def iC (k : ℕ) (i : Fin k) : BB7 k := lift (Sum.inr i)
/-- The `eps` coordinate. -/
def iEps (k : ℕ) : BB7 k :=
  Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1)))))))
/-- The `x` coordinate. -/
def iX (k : ℕ) : BB7 k :=
  Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1))))))
/-- The `u` coordinate (the slack copy of `2 * x`). -/
def iU (k : ℕ) : BB7 k := Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1)))))
/-- The `y` coordinate. -/
def iY (k : ℕ) : BB7 k := Sum.inl (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1))))
/-- The `y'` coordinate. -/
def iYp (k : ℕ) : BB7 k := Sum.inl (Sum.inl (Sum.inr (0 : Fin 1)))
/-- The `z` coordinate (the slack copy of `eps * x - 1`). -/
def iZ (k : ℕ) : BB7 k := Sum.inl (Sum.inr (0 : Fin 1))
/-- The `w` coordinate (the slack copy of `eps ^ 2 * y ^ 2 - (y' - lam * y) ^ 2`). -/
def iW (k : ℕ) : BB7 k := Sum.inr (0 : Fin 1)

/-- The selection map picking `(x, y, c 0 … c (k-1))`. -/
def selY (k : ℕ) : Fin (k + 2) → BB7 k := Fin.cons (iX k) (Fin.cons (iY k) (iC k))
/-- The selection map picking `(u, y', c 0 … c (k-1))`. -/
def selU (k : ℕ) : Fin (k + 2) → BB7 k := Fin.cons (iU k) (Fin.cons (iYp k) (iC k))

/-! ## 2. The rexp-polynomials of the body -/

/-- `z ^ 2 = eps * x - 1`. -/
def PZpoly (k : ℕ) : MvPolynomial (BB7 k ⊕ BB7 k) ℝ :=
  X (Sum.inl (iZ k)) ^ 2 - X (Sum.inl (iEps k)) * X (Sum.inl (iX k)) + 1
/-- `u = 2 * x`. -/
def PUpoly (k : ℕ) : MvPolynomial (BB7 k ⊕ BB7 k) ℝ :=
  X (Sum.inl (iU k)) - C 2 * X (Sum.inl (iX k))
/-- `w ^ 2 = eps ^ 2 * y ^ 2 - (y' - lam * y) ^ 2`. -/
def PWpoly (k : ℕ) : MvPolynomial (BB7 k ⊕ BB7 k) ℝ :=
  X (Sum.inl (iW k)) ^ 2 - X (Sum.inl (iEps k)) ^ 2 * X (Sum.inl (iY k)) ^ 2
    + (X (Sum.inl (iYp k)) - X (Sum.inl (iLam k)) * X (Sum.inl (iY k))) ^ 2

/-- The body: `(x,y,c) ∈ Y`, `(u,y',c) ∈ Y`, the three equations, and `y ≠ 0`, `w ≠ 0`. -/
def Body (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) : Set (BB7 k → ℝ) :=
  {z : BB7 k → ℝ | z ∘ selY k ∈ Y} ∩ {z : BB7 k → ℝ | z ∘ selU k ∈ Y} ∩
  {z : BB7 k → ℝ | rexpEval z (PZpoly k) = 0} ∩
  {z : BB7 k → ℝ | rexpEval z (PUpoly k) = 0} ∩
  {z : BB7 k → ℝ | rexpEval z (PWpoly k) = 0} ∩
  {z : BB7 k → ℝ | z (iY k) ≠ 0} ∩ {z : BB7 k → ℝ | z (iW k) ≠ 0}

/-! ## 3. The six-fold projection and the set `D` -/

/-- The nested tuple obtained from `z1` by adjoining the six slack witnesses, in the order
`x`, `u`, `y`, `y'`, `z`, `w`. -/
def zz7 {k : ℕ} (z1 : BB1 k → ℝ) (ax au ay ayp az aw : ℝ) : BB7 k → ℝ :=
  Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim z1 (fun _ : Fin 1 => ax))
    (fun _ : Fin 1 => au)) (fun _ : Fin 1 => ay)) (fun _ : Fin 1 => ayp))
    (fun _ : Fin 1 => az)) (fun _ : Fin 1 => aw)

/-- The six-fold existential projection of a subset of `ℝ ^ BB7 k`. -/
def Proj6 (k : ℕ) (X : Set (BB7 k → ℝ)) : Set (BB1 k → ℝ) :=
  {z1 | ∃ ax, Sum.elim z1 (fun _ : Fin 1 => ax) ∈
    {z2 : BB2 k → ℝ | ∃ au, Sum.elim z2 (fun _ : Fin 1 => au) ∈
      {z3 : BB3 k → ℝ | ∃ ay, Sum.elim z3 (fun _ : Fin 1 => ay) ∈
        {z4 : BB4 k → ℝ | ∃ ayp, Sum.elim z4 (fun _ : Fin 1 => ayp) ∈
          {z5 : BB5 k → ℝ | ∃ az, Sum.elim z5 (fun _ : Fin 1 => az) ∈
            {z6 : BB6 k → ℝ | ∃ aw, Sum.elim z6 (fun _ : Fin 1 => aw) ∈ X}}}}}}

/-- `D`: the parameters `(lam, c, eps)` for which there exist `x y y'` with `1 ≤ eps * x`,
`(x,y,c) ∈ Y`, `y ≠ 0`, `(2x, y', c) ∈ Y` and `(y' - lam * y) ^ 2 < eps ^ 2 * y ^ 2`. -/
def Dset (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) : Set (BB1 k → ℝ) :=
  {z | ∃ x y y' : ℝ, 1 ≤ z (Sum.inr (0 : Fin 1)) * x ∧
      Fin.cons x (Fin.cons y (fun i => z (Sum.inl (Sum.inr i)))) ∈ Y ∧ y ≠ 0 ∧
      Fin.cons (2 * x) (Fin.cons y' (fun i => z (Sum.inl (Sum.inr i)))) ∈ Y ∧
      (y' - z (Sum.inl (Sum.inl (0 : Fin 1))) * y) ^ 2
        < z (Sum.inr (0 : Fin 1)) ^ 2 * y ^ 2}

/-! ## 4. Bookkeeping lemmas -/

theorem comp_selY {k : ℕ} (z : BB7 k → ℝ) :
    z ∘ selY k = Fin.cons (z (iX k)) (Fin.cons (z (iY k)) (fun i => z (iC k i))) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j => induction j using Fin.cases with | zero => rfl | succ m => rfl

theorem comp_selU {k : ℕ} (z : BB7 k → ℝ) :
    z ∘ selU k = Fin.cons (z (iU k)) (Fin.cons (z (iYp k)) (fun i => z (iC k i))) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j => induction j using Fin.cases with | zero => rfl | succ m => rfl

theorem rexpEval_PZpoly {k : ℕ} (z : BB7 k → ℝ) :
    rexpEval z (PZpoly k) = z (iZ k) ^ 2 - z (iEps k) * z (iX k) + 1 := by simp [PZpoly]

theorem rexpEval_PUpoly {k : ℕ} (z : BB7 k → ℝ) :
    rexpEval z (PUpoly k) = z (iU k) - 2 * z (iX k) := by simp [PUpoly]

theorem rexpEval_PWpoly {k : ℕ} (z : BB7 k → ℝ) :
    rexpEval z (PWpoly k) = z (iW k)^2 - z (iEps k)^2 * z (iY k)^2
      + (z (iYp k) - z (iLam k) * z (iY k))^2 := by simp [PWpoly]

/-- Membership in the body, as an explicit conjunction. -/
theorem mem_body {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {z : BB7 k → ℝ} :
    z ∈ Body k Y ↔ (z ∘ selY k ∈ Y) ∧ (z ∘ selU k ∈ Y) ∧ rexpEval z (PZpoly k) = 0 ∧
      rexpEval z (PUpoly k) = 0 ∧ rexpEval z (PWpoly k) = 0 ∧ z (iY k) ≠ 0 ∧ z (iW k) ≠ 0 := by
  simp only [Body, Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]

/-- Membership in the six-fold projection. -/
theorem proj6_mem {k : ℕ} {X : Set (BB7 k → ℝ)} {z1 : BB1 k → ℝ} :
    z1 ∈ Proj6 k X ↔ ∃ ax au ay ayp az aw, zz7 z1 ax au ay ayp az aw ∈ X := Iff.rfl

theorem zz7_iX {k : ℕ} (z1 : BB1 k → ℝ) (ax au ay ayp az aw : ℝ) :
    zz7 z1 ax au ay ayp az aw (iX k) = ax := by
  simp [zz7, iX, iEps, iU, iY, iYp, iZ, iW, iLam, iC, lift]

theorem zz7_iU {k : ℕ} (z1 : BB1 k → ℝ) (ax au ay ayp az aw : ℝ) :
    zz7 z1 ax au ay ayp az aw (iU k) = au := by
  simp [zz7, iX, iEps, iU, iY, iYp, iZ, iW, iLam, iC, lift]

theorem zz7_iY {k : ℕ} (z1 : BB1 k → ℝ) (ax au ay ayp az aw : ℝ) :
    zz7 z1 ax au ay ayp az aw (iY k) = ay := by
  simp [zz7, iX, iEps, iU, iY, iYp, iZ, iW, iLam, iC, lift]

theorem zz7_iYp {k : ℕ} (z1 : BB1 k → ℝ) (ax au ay ayp az aw : ℝ) :
    zz7 z1 ax au ay ayp az aw (iYp k) = ayp := by
  simp [zz7, iX, iEps, iU, iY, iYp, iZ, iW, iLam, iC, lift]

theorem zz7_iZ {k : ℕ} (z1 : BB1 k → ℝ) (ax au ay ayp az aw : ℝ) :
    zz7 z1 ax au ay ayp az aw (iZ k) = az := by
  simp [zz7, iX, iEps, iU, iY, iYp, iZ, iW, iLam, iC, lift]

theorem zz7_iW {k : ℕ} (z1 : BB1 k → ℝ) (ax au ay ayp az aw : ℝ) :
    zz7 z1 ax au ay ayp az aw (iW k) = aw := by
  simp [zz7, iX, iEps, iU, iY, iYp, iZ, iW, iLam, iC, lift]

theorem zz7_iEps {k : ℕ} (z1 : BB1 k → ℝ) (ax au ay ayp az aw : ℝ) :
    zz7 z1 ax au ay ayp az aw (iEps k) = z1 (Sum.inr (0 : Fin 1)) := by
  simp [zz7, iX, iEps, iU, iY, iYp, iZ, iW, iLam, iC, lift]

theorem zz7_iLam {k : ℕ} (z1 : BB1 k → ℝ) (ax au ay ayp az aw : ℝ) :
    zz7 z1 ax au ay ayp az aw (iLam k) = z1 (Sum.inl (Sum.inl (0 : Fin 1))) := by
  simp [zz7, iX, iEps, iU, iY, iYp, iZ, iW, iLam, iC, lift]

theorem zz7_iC {k : ℕ} (z1 : BB1 k → ℝ) (ax au ay ayp az aw : ℝ) (i : Fin k) :
    zz7 z1 ax au ay ayp az aw (iC k i) = z1 (Sum.inl (Sum.inr i)) := by
  simp [zz7, iX, iEps, iU, iY, iYp, iZ, iW, iLam, iC, lift]

/-- The body conditions, read on the nested tuple `zz7`. -/
theorem zz7_mem_body {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} (z1 : BB1 k → ℝ)
    (ax au ay ayp az aw : ℝ) :
    zz7 z1 ax au ay ayp az aw ∈ Body k Y ↔
      Fin.cons ax (Fin.cons ay (fun i => z1 (Sum.inl (Sum.inr i)))) ∈ Y ∧
      Fin.cons au (Fin.cons ayp (fun i => z1 (Sum.inl (Sum.inr i)))) ∈ Y ∧
      az ^ 2 = z1 (Sum.inr (0 : Fin 1)) * ax - 1 ∧ au = 2 * ax ∧
      aw ^ 2 = z1 (Sum.inr (0 : Fin 1)) ^ 2 * ay ^ 2
        - (ayp - z1 (Sum.inl (Sum.inl (0 : Fin 1))) * ay) ^ 2 ∧
      ay ≠ 0 ∧ aw ≠ 0 := by
  rw [mem_body]
  simp only [comp_selY, comp_selU, rexpEval_PZpoly, rexpEval_PUpoly, rexpEval_PWpoly,
    zz7_iX, zz7_iU, zz7_iY, zz7_iYp, zz7_iZ, zz7_iW, zz7_iEps, zz7_iLam, zz7_iC]
  constructor
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7⟩
    exact ⟨h1,h2, by linarith, by linarith, by linarith, h6, h7⟩
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7⟩
    exact ⟨h1,h2, by linarith, by linarith, by linarith, h6, h7⟩

/-- **The key reduction.**  Projecting the six slack coordinates `x, u, y, y', z, w` away from
the body gives exactly the set `D`. -/
theorem proj6_body_mem {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (z1 : BB1 k → ℝ) :
    z1 ∈ Proj6 k (Body k Y) ↔ z1 ∈ Dset k Y := by
  rw [proj6_mem]
  simp only [Dset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ax, au, ay, ayp, az, aw, hb⟩
    rw [zz7_mem_body] at hb
    obtain ⟨hY1, hY2, hz, hu, hw, hay, haw⟩ := hb
    exact ⟨ax, ay, ayp, by nlinarith [sq_nonneg az], hY1, hay, by rw [← hu]; exact hY2,
      by have := sq_pos_of_ne_zero haw; nlinarith⟩
  · rintro ⟨x, y, y', h1, hY1, hy, hY2, h5⟩
    refine ⟨x, 2 * x, y, y', Real.sqrt (z1 (Sum.inr 0) * x - 1),
      Real.sqrt (z1 (Sum.inr 0) ^ 2 * y ^ 2 - (y' - z1 (Sum.inl (Sum.inl 0)) * y) ^ 2), ?_⟩
    rw [zz7_mem_body]
    exact ⟨hY1, hY2, by rw [Real.sq_sqrt]; linarith, rfl,
      by rw [Real.sq_sqrt]; linarith, hy,
      ne_of_gt (Real.sqrt_pos_of_pos (by linarith))⟩

end Work.WilC4aU
