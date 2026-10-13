import Mathlib
import Submission.Work.WilG4c.CurveFamDefs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG4c.CurveFam.badSet_mem
import Submission.Work.WilG4c.CurveFam.graphOf_sel_eq_coordImage
import Submission.Work.WilG4c.CurveFam.mem_badSet_iff

set_option autoImplicit false

noncomputable section

open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG5

variable {p n : ℕ}

/-! ## 1. Elementary facts about `DgSet` and the index maps -/

/-- Membership in the `x`-derivative graph. -/
theorem mem_DgSet {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {z : Fin (p + (n + 1) + 1) → ℝ} :
    z ∈ DgSet p n f ↔ Fin.init z ∈ LocSet p n f ∧
      z (Fin.last (p + (n + 1))) = xDer p n f (Fin.init z) := by
  simp only [DgSet, LocSet, xDer, Set.mem_ofPred_eq, iteratedFDeriv_one_apply]

/-- The `C¹` locus is the projection of the derivative graph. -/
theorem projLast_DgSet (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    projLast (DgSet p n f) = LocSet p n f := by
  ext x
  constructor
  · rintro ⟨t, ht⟩
    rw [mem_DgSet, Fin.init_snoc] at ht
    exact ht.1
  · intro hx
    refine ⟨xDer p n f x, ?_⟩
    rw [mem_DgSet, Fin.init_snoc, Fin.snoc_last]
    exact ⟨hx, rfl⟩

@[simp] theorem xDer_xPt (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) :
    xDer p n f (xPt l x y) = xDeriv f l x y := rfl

@[simp] theorem xPt_yIdx (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) (j : Fin n) :
    xPt l x y (yIdx p n j) = y j := by
  rw [xPt, yIdx, Fin.append_right, Fin.cons_succ]

theorem zPt_xPt (l : Fin p → ℝ) (x : ℝ) (y y' : Fin n → ℝ) :
    zPt p n (xPt l x y) y' = xPt l x y' := by
  have h1 : (xPt l x y) ∘ Fin.castAdd (n + 1) = l := by
    funext i
    rw [Function.comp_apply, xPt, Fin.append_left]
  have h2 : xPt l x y (Fin.natAdd p 0) = x := by
    rw [xPt, Fin.append_right, Fin.cons_zero]
  rw [zPt, h1, h2, xPt]

/-- For reals, `4 a² < b²` is `2|a| < |b|`. -/
theorem four_sq_lt_iff (a b : ℝ) : 4 * a ^ 2 < b ^ 2 ↔ 2 * |a| < |b| := by
  rw [← sq_abs a, ← sq_abs b, show (4 : ℝ) * |a| ^ 2 = (2 * |a|) ^ 2 by ring]
  rw [sq_lt_sq, abs_of_nonneg (by positivity), abs_abs]

/-- `Fin.append (Fin.snoc l x) y` and `xPt l x y` differ only by the associativity of the
index type. -/
theorem cast_snoc_append_xPt (h : p + (n + 1) = (p + 1) + n) (l : Fin p → ℝ) (x : ℝ)
    (y : Fin n → ℝ) :
    (fun i : Fin (p + (n + 1)) => Fin.append (Fin.snoc l x) y (Fin.cast h i))
      = xPt l x y := by
  funext i
  refine Fin.addCases (m := p) (n := n + 1) (fun j => ?_) (fun u => ?_) i
  · have h1 : Fin.cast h (Fin.castAdd (n + 1) j) = Fin.castAdd n (Fin.castSucc j) :=
      Fin.ext rfl
    rw [h1, Fin.append_left, Fin.snoc_castSucc, xPt, Fin.append_left]
  · induction u using Fin.cases with
    | zero =>
      have h2 : Fin.cast h (Fin.natAdd p 0) = Fin.castAdd n (Fin.last p) := Fin.ext rfl
      rw [h2, Fin.append_left, Fin.snoc_last, xPt, Fin.append_right, Fin.cons_zero]
    | succ j =>
      have h3 : Fin.cast h (Fin.natAdd p j.succ) = Fin.natAdd (p + 1) j := by
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
        omega
      rw [h3, Fin.append_right, xPt, Fin.append_right, Fin.cons_succ]

/-! ## 2. Combinators for the `Ω`-calculus with plain natural degrees -/

theorem inter2_nat {S : SOMin} {n : ℕ} {a1 a2 D1 D2 : ℕ} {X Y : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω a1 D1 n) (hY : Y ∈ S.Ω a2 D2 n) :
    X ∩ Y ∈ S.Ω (max a1 a2 + 1) (D1 + D2) n := by
  have h1 : X ∈ S.Ω (max a1 a2) D1 n := mem_mono hX _ _ (le_max_left _ _) le_rfl
  have h2 : Y ∈ S.Ω (max a1 a2) D2 n := mem_mono hY _ _ (le_max_right _ _) le_rfl
  have h := S.inter (F := max a1 a2) (n := n) (k := 2)
    (fun i : Fin 2 => if i = 0 then D1 else D2)
    (fun i : Fin 2 => if i = 0 then X else Y)
    (by intro i; fin_cases i <;> simpa)
  rw [Work.WilG1.Omega.iInter_fin_two] at h
  have hsum : (∑ i : Fin 2, (if i = 0 then D1 else D2)) = D1 + D2 := by
    simp [Fin.sum_univ_two]
  rw [hsum] at h
  exact h

/-- `Xset` is an `Ω`-set (given the `Ω`-membership of the selection set `badSet`). -/
theorem Xset_mem {S : SOMin} {p n a1 L : ℕ}
    {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    (hDg : DgSet p n f ∈ S.Ω a1 L (p + (n + 1) + 1)) :
    Xset p n f ∈ S.Ω (Fx p n a1) (Dx p n L) (p + (n + 1)) := by
  have hloc : LocSet p n f ∈ S.Ω (a1 + 1) L (p + (n + 1)) := by
    rw [← projLast_DgSet]
    exact S.proj hDg
  have hbad : badSet p n f ∈ S.Ω (Fbad p n a1) (Dbad p n L) (p + (n + 1)) :=
    Work.WilG4c.CurveFam.badSet_mem hDg
  have hcube : coordPre (yIdx p n) (openCube n) ∈ S.Ω (Fx p n a1 - 1)
      ((16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32) (p + (n + 1)) :=
    mem_mono (coordPre_mem (S := S) (openCube_mem (S := S) (n := n))) _ _
      (by simp only [Fx]; omega) le_rfl
  have hl' : LocSet p n f ∈ S.Ω (Fx p n a1 - 1) L (p + (n + 1)) :=
    mem_mono hloc _ _ (by simp only [Fx]; omega) le_rfl
  have hb' : (badSet p n f)ᶜ ∈ S.Ω (Fx p n a1 - 1) (Dbad p n L) (p + (n + 1)) :=
    mem_mono (S.compl hbad) _ _ (by simp only [Fx, Fbad]; omega) le_rfl
  have hint := S.inter (F := Fx p n a1 - 1) (n := p + (n + 1)) (k := 3)
    (fun i : Fin 3 => ![(16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32, L, Dbad p n L] i)
    (fun i : Fin 3 => ![(coordPre (yIdx p n) (openCube n)), LocSet p n f,
      (badSet p n f)ᶜ] i)
    (by intro i; fin_cases i <;> simpa)
  have hsum : (∑ i : Fin 3,
      ![(16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32, L, Dbad p n L] i)
      = ((16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32) + L + Dbad p n L := by
    simp [Fin.sum_univ_three]
  rw [hsum] at hint
  have hset : Xset p n f = ⋂ i : Fin 3,
      ![(coordPre (yIdx p n) (openCube n)), LocSet p n f, (badSet p n f)ᶜ] i := by
    rw [Xset]
    ext w
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩ i
      fin_cases i
      · simpa using h1
      · simpa using h2
      · simpa using h3
    · intro h
      exact ⟨⟨by simpa using h 0, by simpa using h 1⟩, by simpa using h 2⟩
  rw [hset]
  have hunfF : Fx p n a1 = a1 + 1000 * (p + n + 2) + 20000 := rfl
  have hunfD : Dx p n L = 3 * L + (1000 * (p + n + 2) + 10000) := rfl
  have hunfB : Dbad p n L = 2 * L + 600 * (p + n + 2) + 5000 := rfl
  refine mem_mono hint (Fx p n a1) (Dx p n L) ?_ ?_
  · rw [hunfF]; omega
  · rw [hunfD, hunfB]; omega

/-- The unfolding of `Xset` into the cube/`C¹`-locus/near-maximality conditions. -/
theorem mem_Xset_iff {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    (hmb : ∀ w : Fin (p + (n + 1)) → ℝ,
      (w ∈ badSet p n f ↔ ∃ y' : Fin n → ℝ, y' ∈ openCube n ∧ w ∈ LocSet p n f ∧
        zPt p n w y' ∈ LocSet p n f ∧
        4 * (xDer p n f w) ^ 2 < (xDer p n f (zPt p n w y')) ^ 2))
    (w : Fin (p + (n + 1)) → ℝ) :
    w ∈ Xset p n f ↔ (fun j : Fin n => w (yIdx p n j)) ∈ openCube n ∧ w ∈ LocSet p n f ∧
      ∀ y' : Fin n → ℝ, y' ∈ openCube n → zPt p n w y' ∈ LocSet p n f →
        |xDer p n f (zPt p n w y')| ≤ 2 * |xDer p n f w| := by
  simp only [Xset, Set.mem_inter_iff, Set.mem_compl_iff, coordPre, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hc, hl⟩, hb⟩
    refine ⟨hc, hl, ?_⟩
    intro y' hy' hl'
    by_contra hcon
    have hlt : 2 * |xDer p n f w| < |xDer p n f (zPt p n w y')| := lt_of_not_ge hcon
    exact hb ((hmb w).mpr ⟨y', hy', hl, hl', (four_sq_lt_iff _ _).mpr hlt⟩)
  · rintro ⟨hc, hl, hmax⟩
    refine ⟨⟨hc, hl⟩, ?_⟩
    intro hb
    obtain ⟨y', hy', _, hl', h4⟩ := (hmb w).mp hb
    exact absurd (hmax y' hy' hl') (not_le.mpr ((four_sq_lt_iff _ _).mp h4))

/-- The degree of the graph coordinates produced by `CurveFam`, as the evaluation of the
polynomial supplied there. -/
theorem eval_curveB (b1 : MvPolynomial (Fin 2) ℕ) (bC : Polynomial ℕ) (p n D : ℕ) :
    MvPolynomial.eval ![D, 0]
        ((Polynomial.toMvPolynomial (0 : Fin 2))
          (Polynomial.C (32 * (((p + 1) + n) + (p + 1 + 1)) + 32) +
            bC.comp (Polynomial.C (Cx p n) + Polynomial.C 3 * Work.WilG1.psubst b1 1)))
      = bC.eval (Dx p n (MvPolynomial.eval ![D, 1] b1)) +
        (32 * (((p + 1) + n) + (p + 1 + 1)) + 32) := by
  have harg : Polynomial.eval D
      (Polynomial.C (Cx p n) + Polynomial.C 3 * Work.WilG1.psubst b1 1)
      = Dx p n (MvPolynomial.eval ![D, 1] b1) := by
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C,
      Work.WilG1.eval_psubst, Dx]
    ring
  rw [MvPolynomial.eval_toMvPolynomial, Matrix.cons_val_zero, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_comp, harg]
  omega

theorem CurveFam (S : WilkiesDesign.SOMin) (hder : S.SharpDeriv) (hchoice : Work.WilkG4c.ChoiceHyp S) (n p : ℕ) :
    ∀ (F0 : ℕ), ∃ (A : ℕ) (B : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (Λ : Set (Fin p → ℝ)) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
        ∃ γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ),
          (∀ j : Fin n, WilkiesDesign.graphOf (fun w : Fin (p + 1) → ℝ =>
              γ (fun i => w (Fin.castSucc i)) (w (Fin.last p)) j)
            ∈ S.Ω A (MvPolynomial.eval ![D, 0] B) (p + 1 + 1)) ∧
          (∀ l ∈ Λ, ∀ x : ℝ,
            (∃ y : Fin n → ℝ, y ∈ WilkiesDesign.openCube n ∧
              Work.WilkG4c.xPt l x y ∈ interior {z | ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat f) z} ∧
              ∀ y' : Fin n → ℝ, y' ∈ WilkiesDesign.openCube n →
                Work.WilkG4c.xPt l x y' ∈ interior {z | ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat f) z} →
                |Work.WilkG4c.xDeriv f l x y'| ≤ 2 * |Work.WilkG4c.xDeriv f l x y|) →
            γ l x ∈ WilkiesDesign.openCube n ∧
            Work.WilkG4c.xPt l x (γ l x) ∈ interior {z | ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat f) z} ∧
            ∀ y' : Fin n → ℝ, y' ∈ WilkiesDesign.openCube n →
              Work.WilkG4c.xPt l x y' ∈ interior {z | ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat f) z} →
              |Work.WilkG4c.xDeriv f l x y'| ≤ 2 * |Work.WilkG4c.xDeriv f l x (γ l x)|) := by
  intro F0
  obtain ⟨a1, b1, hder1⟩ := hder F0 (p + (n + 1))
  obtain ⟨aC, bC, hC⟩ := hchoice (Fx p n a1) (p + 1) n
  refine ⟨aC + 64 * (((p + 1) + n) + (p + 1 + 1)) + 64,
    (Polynomial.toMvPolynomial (0 : Fin 2))
      (Polynomial.C (32 * (((p + 1) + n) + (p + 1 + 1)) + 32) +
        bC.comp (Polynomial.C (Cx p n) + Polynomial.C 3 * Work.WilG1.psubst b1 1)), ?_⟩
  intro D Λ f hΩ
  have hgraph : graphOf (famFunHat f) ∈ S.Ω F0 D (p + (n + 1) + 1) := by
    rw [← famGraph_eq_graphOf_famFunHat]
    exact hΩ
  have hDg : DgSet p n f ∈ S.Ω a1 (MvPolynomial.eval ![D, 1] b1) (p + (n + 1) + 1) :=
    hder1 D (famFunHat f) hgraph 1 (fun _ : Fin 1 => xDirHat p n)
  have hmb : ∀ w : Fin (p + (n + 1)) → ℝ,
      (w ∈ badSet p n f ↔ ∃ y' : Fin n → ℝ, y' ∈ openCube n ∧ w ∈ LocSet p n f ∧
        zPt p n w y' ∈ LocSet p n f ∧
        4 * (xDer p n f w) ^ 2 < (xDer p n f (zPt p n w y')) ^ 2) := by
    intro w
    exact Work.WilG4c.CurveFam.mem_badSet_iff f w
  have hXmem : Xset p n f ∈
      S.Ω (Fx p n a1) (Dx p n (MvPolynomial.eval ![D, 1] b1)) (p + (n + 1)) := Xset_mem hDg
  have hPL : p + (n + 1) = (p + 1) + n := by omega
  have hXmem' : (hPL ▸ Xset p n f) ∈
      S.Ω (Fx p n a1) (Dx p n (MvPolynomial.eval ![D, 1] b1)) ((p + 1) + n) :=
    omega_ndrec hPL hXmem
  obtain ⟨fsel, hsel, hGmem⟩ := hC (Dx p n (MvPolynomial.eval ![D, 1] b1))
    (hPL ▸ Xset p n f) hXmem'
  refine ⟨fun l x => fsel (Fin.snoc l x), ?_, ?_⟩
  · intro j
    have hmem := coordImage_mem (S := S)
      (ι := Fin.snoc (fun i : Fin (p + 1) => Fin.castAdd n i) (Fin.natAdd (p + 1) j)) hGmem
    have hge : graphOf (fun w : Fin (p + 1) → ℝ =>
        fsel (Fin.snoc (Fin.init w) (w (Fin.last p))) j)
        = coordImage (Fin.snoc (fun i : Fin (p + 1) => Fin.castAdd n i)
            (Fin.natAdd (p + 1) j))
          {z : Fin ((p + 1) + n) → ℝ | ∀ k : Fin n,
            z (Fin.natAdd (p + 1) k) = fsel (fun i => z (Fin.castAdd n i)) k} :=
      Work.WilG4c.CurveFam.graphOf_sel_eq_coordImage fsel j
    have hfun : (fun w : Fin (p + 1) → ℝ =>
          (fun l x => fsel (Fin.snoc l x)) (fun i => w (Fin.castSucc i)) (w (Fin.last p)) j)
        = (fun w : Fin (p + 1) → ℝ =>
            fsel (Fin.snoc (Fin.init w) (w (Fin.last p))) j) := rfl
    rw [hfun, hge]
    rw [eval_curveB]
    exact hmem
  · intro l hl x hx
    obtain ⟨y, hyc, hyl, hymx⟩ := hx
    have hwit : Fin.append (Fin.snoc l x) y ∈ (hPL ▸ Xset p n f) := by
      rw [mem_ndrec, cast_snoc_append_xPt hPL]
      refine (mem_Xset_iff hmb (xPt l x y)).mpr ⟨?_, hyl, ?_⟩
      · have hyfun : (fun j : Fin n => xPt l x y (yIdx p n j)) = y := by
          funext j; rw [xPt_yIdx]
        rwa [hyfun]
      · intro y' hy' hl'
        rw [zPt_xPt] at hl'
        simpa only [zPt_xPt, xDer_xPt] using hymx y' hy' hl'
    have hmem2 := hsel (Fin.snoc l x) ⟨y, hwit⟩
    have hX : xPt l x (fsel (Fin.snoc l x)) ∈ Xset p n f := by
      have h := (mem_ndrec hPL (Xset p n f)
        (Fin.append (Fin.snoc l x) (fsel (Fin.snoc l x)))).mp hmem2
      rwa [cast_snoc_append_xPt hPL] at h
    obtain ⟨hc, hlLoc, hmax⟩ := (mem_Xset_iff hmb (xPt l x (fsel (Fin.snoc l x)))).mp hX
    refine ⟨?_, hlLoc, ?_⟩
    · have hyfun : (fun j : Fin n => xPt l x (fsel (Fin.snoc l x)) (yIdx p n j))
          = fsel (Fin.snoc l x) := by
        funext j; rw [xPt_yIdx]
      rwa [hyfun] at hc
    · intro y' hy' hl'
      have hl'' : zPt p n (xPt l x (fsel (Fin.snoc l x))) y' ∈ LocSet p n f := by
        rw [zPt_xPt]; exact hl'
      simpa only [zPt_xPt, xDer_xPt] using hmax y' hy' hl''

end Work.WilkG4c

namespace Work.WilG4c

/-- The `CurveFam` lemma under the name used by the problem statement; this is the declaration
`Work.WilkG4c.CurveFam`, whose namespace is the one in which the surrounding vocabulary
(`Work.WilkG4c.xPt`, `Work.WilkG4c.ChoiceHyp`, …) lives. -/
abbrev CurveFam := @Work.WilkG4c.CurveFam

end Work.WilG4c
