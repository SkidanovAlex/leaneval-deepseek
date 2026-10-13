/-
  WilE9G / Lagrange — **supporting definitions for `degen_kernel_iff`**.

  `degen_kernel_iff` relates the kernel of the differential of `degenH` on the kernel of the
  differential of `degenF` to the determinant of `lagJacTrue`.  The proof needs a number of
  auxiliary objects:

  * the indices `degenZK`, `degenNuK`, `degenCK` of the `z`, `(ν,ν₀)` and `c` blocks;
  * the index `degenColK` of the `(yt,ν)`-block (`degenZK` on the last `1+m` coordinates of `z`,
    then `degenNuK`), and the "row transfer" `degenRowInv` between the equation index of the
    constructed stratum and the equation index of `lagJacTrue`;
  * the linear map `degenZLin` and the symbolic gradient `gradZ`;
  * the coordinate functionals `dgLam`, `dgA`, `dgPsi`, `dgCoef` and the assembled derivative
    `dgH` of `degenH`, and `dgF` (the — linear — map `degenF` itself);
  * the embedding `emb` of the reduced variables into the ambient space.

  All statements are collected here so that the lemmas about them can be delegated.
-/
import Mathlib
import Submission.Work.WilE9G.Lagrange.DegenSetup
import Submission.Work.WilE9G.Lagrange.Stratum
import Submission.Work.WilE9G.Lagrange.LagBlocks
import Submission.Work.WilE9G.Jac
import Submission.Work.WilE5.Strat.flatConormalTools

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G.Lagrange
open WilkiesDesign WilkiesDesign.E Work.WilE9G

variable {n m : ℕ}

/-! ## §1. The coordinate indices -/

/-- The ambient index of the `z`-coordinate `i` (the first `n + (1+m)` coordinates). -/
def degenZK (n m : ℕ) {j : ℕ} (i : Fin (n + (1 + m))) : Fin (degenDim n m j) :=
  ⟨i.val, by simp only [degenDim]; omega⟩

/-- The ambient index of the multiplier `ν_a`. -/
def degenNuK (n m : ℕ) {j : ℕ} (a : Fin (j + 1)) : Fin (degenDim n m j) :=
  ⟨n + (1 + m) + a.val, by simp only [degenDim]; omega⟩

/-- The ambient index of the direction coordinate `c_l`. -/
def degenCK (n m : ℕ) {j : ℕ} (l : Fin (1 + m)) : Fin (degenDim n m j) :=
  ⟨n + (1 + m) + (j + 1) + l.val, by simp only [degenDim]; omega⟩

/-- The ambient index of the reduced variable indexed by `col`: the `(1+m)` fibre coordinates of
`z`, then the `j+1` multipliers. -/
def degenColK (n m : ℕ) {j : ℕ} (col : Fin ((1 + m) + (j + 1))) : Fin (degenDim n m j) :=
  Fin.addCases (fun l' : Fin (1 + m) => degenZK n m (j := j) (Fin.natAdd n l'))
    (fun a : Fin (j + 1) => degenNuK n m (j := j) a) col

/-- The equation index of `degenH` (`(h_a, N, ψ_l)`) corresponding to the equation index
`(L_l, h_a, N)` of `lagJacTrue`. -/
def degenRowInv (m : ℕ) {j : ℕ} (r : Fin ((1 + m) + (j + 1))) : Fin (j + (1 + (1 + m))) :=
  Fin.addCases
    (fun l : Fin (1 + m) => Fin.natAdd j (Fin.natAdd 1 l))
    (fun s : Fin (j + 1) =>
      Fin.addCases
        (fun a : Fin j => Fin.castAdd (1 + (1 + m)) a)
        (fun _ : Fin 1 => Fin.natAdd j (Fin.castAdd (1 + m) (0 : Fin 1)))
        s)
    r

@[simp] theorem degenZK_val {j : ℕ} (i : Fin (n + (1 + m))) :
    (degenZK n m (j := j) i).val = i.val := rfl

@[simp] theorem degenNuK_val {j : ℕ} (a : Fin (j + 1)) :
    (degenNuK n m (j := j) a).val = n + (1 + m) + a.val := rfl

@[simp] theorem degenCK_val {j : ℕ} (l : Fin (1 + m)) :
    (degenCK n m (j := j) l).val = n + (1 + m) + (j + 1) + l.val := rfl

@[simp] theorem degenColK_castAdd {j : ℕ} (l' : Fin (1 + m)) :
    degenColK n m (j := j) (Fin.castAdd (j + 1) l')
      = degenZK n m (j := j) (Fin.natAdd n l') :=
  Fin.addCases_left (motive := fun _ => Fin (degenDim n m j)) l'

@[simp] theorem degenColK_natAdd {j : ℕ} (a : Fin (j + 1)) :
    degenColK n m (j := j) (Fin.natAdd (1 + m) a) = degenNuK n m (j := j) a :=
  Fin.addCases_right (motive := fun _ => Fin (degenDim n m j)) a

@[simp] theorem degenZ_apply_k {j : ℕ} (p : Fin (degenDim n m j) → ℝ) (i : Fin (n + (1 + m))) :
    degenZ p i = p (degenZK n m (j := j) i) := rfl

@[simp] theorem degenNu_apply_k {j : ℕ} (p : Fin (degenDim n m j) → ℝ) (a : Fin (j + 1)) :
    degenNu p a = p (degenNuK n m (j := j) a) := rfl

@[simp] theorem degenC_apply_k {j : ℕ} (p : Fin (degenDim n m j) → ℝ) (l : Fin (1 + m)) :
    degenC p l = p (degenCK n m (j := j) l) := rfl

theorem degenZK_injective {j : ℕ} :
    Function.Injective (degenZK n m (j := j) : Fin (n + (1 + m)) → Fin (degenDim n m j)) :=
  fun a b h => Fin.ext (by simpa only [degenZK_val] using congrArg Fin.val h)

theorem degenNuK_injective {j : ℕ} :
    Function.Injective (degenNuK n m (j := j) : Fin (j + 1) → Fin (degenDim n m j)) :=
  fun a b h => Fin.ext (by
    have := congrArg Fin.val h; rw [degenNuK_val, degenNuK_val] at this; omega)

theorem degenZK_ne_degenNuK {j : ℕ} (i : Fin (n + (1 + m))) (a : Fin (j + 1)) :
    degenZK n m (j := j) i ≠ degenNuK n m (j := j) a := by
  intro h; have := congrArg Fin.val h; rw [degenZK_val, degenNuK_val] at this; omega

theorem degenZK_ne_degenCK {j : ℕ} (i : Fin (n + (1 + m))) (l : Fin (1 + m)) :
    degenZK n m (j := j) i ≠ degenCK n m (j := j) l := by
  intro h; have := congrArg Fin.val h; rw [degenZK_val, degenCK_val] at this; omega

theorem degenNuK_ne_degenCK {j : ℕ} (a : Fin (j + 1)) (l : Fin (1 + m)) :
    degenNuK n m (j := j) a ≠ degenCK n m (j := j) l := by
  intro h; have := congrArg Fin.val h; rw [degenNuK_val, degenCK_val] at this; omega

/-- The value of the reduced index: `degenColK` is the "shift by `n`" of the reduced index. -/
theorem degenColK_val {j : ℕ} (c : Fin ((1 + m) + (j + 1))) :
    (degenColK n m (j := j) c).val = n + c.val := by
  revert c
  refine Fin.addCases ?_ ?_
  · intro l'
    rw [degenColK_castAdd, degenZK_val, Fin.val_natAdd, Fin.val_castAdd]
  · intro a
    rw [degenColK_natAdd, degenNuK_val, Fin.val_natAdd]
    ring

theorem degenColK_val_ge {j : ℕ} (col : Fin ((1 + m) + (j + 1))) :
    n ≤ (degenColK n m (j := j) col).val := by
  rw [degenColK_val]; omega

theorem degenColK_val_lt {j : ℕ} (col : Fin ((1 + m) + (j + 1))) :
    (degenColK n m (j := j) col).val < n + (1 + m) + (j + 1) := by
  rw [degenColK_val]
  have := col.isLt
  omega

theorem degenColK_injective {j : ℕ} :
    Function.Injective (degenColK n m (j := j) :
      Fin ((1 + m) + (j + 1)) → Fin (degenDim n m j)) := by
  intro c d h
  have hv := congrArg Fin.val h
  rw [degenColK_val, degenColK_val] at hv
  exact Fin.ext (by omega)

/-! ## §2. The linear map `degenZLin` and the symbolic gradient `gradZ` -/

/-- The coordinate-selecting linear map `p ↦ degenZ p`. -/
def degenZLin (n m : ℕ) {j : ℕ} : (Fin (degenDim n m j) → ℝ) →L[ℝ] (Fin (n + (1 + m)) → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (degenZK n m (j := j) i))

@[simp] theorem degenZLin_apply' {j : ℕ} (v : Fin (degenDim n m j) → ℝ) (i : Fin (n + (1 + m))) :
    degenZLin n m v i = v (degenZK n m (j := j) i) := rfl

@[simp] theorem degenZLin_apply {j : ℕ} (v : Fin (degenDim n m j) → ℝ) :
    degenZLin n m v = degenZ v := by funext i; rfl

/-- The symbolic gradient of `eaEval c Q ∘ degenZ` at `p`. -/
def gradZ (n m : ℕ) {j r : ℕ} (c : EAChain (n + (1 + m)) r) (Q : EAPoly (n + (1 + m)) r)
    (p : Fin (degenDim n m j) → ℝ) : (Fin (degenDim n m j) → ℝ) →L[ℝ] ℝ :=
  (∑ i : Fin (n + (1 + m)), eaEval c (eaD c i Q) (degenZ p) •
    (ContinuousLinearMap.proj i)).comp (degenZLin n m (j := j))

theorem hasFDerivAt_degenZ_eval {j r : ℕ} (c : EAChain (n + (1 + m)) r)
    (Q : EAPoly (n + (1 + m)) r) (p : Fin (degenDim n m j) → ℝ) :
    HasFDerivAt (fun p => eaEval c Q (degenZ p)) (gradZ n m c Q p) p := by
  have hZ : HasFDerivAt (fun (p : Fin (degenDim n m j) → ℝ) => degenZ p)
      (degenZLin n m (j := j)) p :=
    (degenZLin n m (j := j)).hasFDerivAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun v => degenZLin_apply v)
  exact (Work.WilE5.Calc.hasFDerivAt_eaEval c Q (degenZ p)).comp p hZ

theorem fderiv_degenZ_eval {j r : ℕ} (c : EAChain (n + (1 + m)) r)
    (Q : EAPoly (n + (1 + m)) r) (p : Fin (degenDim n m j) → ℝ) :
    fderiv ℝ (fun p => eaEval c Q (degenZ p)) p = gradZ n m c Q p :=
  (hasFDerivAt_degenZ_eval c Q p).fderiv

theorem gradZ_apply_single_zk {j r : ℕ} (c : EAChain (n + (1 + m)) r)
    (Q : EAPoly (n + (1 + m)) r) (p : Fin (degenDim n m j) → ℝ) (i : Fin (n + (1 + m))) :
    gradZ n m c Q p (Pi.single (degenZK n m (j := j) i) 1) = eaEval c (eaD c i Q) (degenZ p) := by
  rw [gradZ, ContinuousLinearMap.comp_apply]
  have hlin : degenZLin n m (Pi.single (degenZK n m (j := j) i) 1) = Pi.single i 1 := by
    funext i'
    rw [degenZLin_apply']
    simp only [Pi.single_apply, degenZK_injective.eq_iff]
  rw [hlin]
  exact Work.WilE5.Strat.sum_smul_proj_single _ i

theorem gradZ_apply_single_nuk {j r : ℕ} (c : EAChain (n + (1 + m)) r)
    (Q : EAPoly (n + (1 + m)) r) (p : Fin (degenDim n m j) → ℝ) (a : Fin (j + 1)) :
    gradZ n m c Q p (Pi.single (degenNuK n m (j := j) a) 1) = 0 := by
  rw [gradZ, ContinuousLinearMap.comp_apply]
  have hlin : degenZLin n m (Pi.single (degenNuK n m (j := j) a) 1) = 0 := by
    funext i'
    rw [degenZLin_apply', Pi.single_apply]
    simp only [Pi.zero_apply]
    exact ite_eq_right (degenZK_ne_degenNuK i' a)
  rw [hlin]
  simp

theorem gradZ_apply_single_ck {j r : ℕ} (c : EAChain (n + (1 + m)) r)
    (Q : EAPoly (n + (1 + m)) r) (p : Fin (degenDim n m j) → ℝ) (l : Fin (1 + m)) :
    gradZ n m c Q p (Pi.single (degenCK n m (j := j) l) 1) = 0 := by
  rw [gradZ, ContinuousLinearMap.comp_apply]
  have hlin : degenZLin n m (Pi.single (degenCK n m (j := j) l) 1) = 0 := by
    funext i'
    rw [degenZLin_apply', Pi.single_apply]
    simp only [Pi.zero_apply]
    exact ite_eq_right (degenZK_ne_degenCK i' l)
  rw [hlin]
  simp

/-! ## §3. Derivatives of the coordinate functions and of `degenH` -/

theorem hasFDerivAt_degenNu {j : ℕ} (a : Fin (j + 1)) (p : Fin (degenDim n m j) → ℝ) :
    HasFDerivAt (fun p => degenNu p a)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (degenDim n m j) => ℝ)
        (degenNuK n m (j := j) a)) p := by
  have hfun : (fun p : Fin (degenDim n m j) → ℝ => degenNu p a)
      = ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (degenDim n m j) => ℝ)
          (degenNuK n m (j := j) a)) := rfl
  have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (degenDim n m j) => ℝ)
    (degenNuK n m (j := j) a)).hasFDerivAt (x := p)
  rwa [← hfun] at this

theorem hasFDerivAt_degenC {j : ℕ} (l : Fin (1 + m)) (p : Fin (degenDim n m j) → ℝ) :
    HasFDerivAt (fun p => degenC p l)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (degenDim n m j) => ℝ)
        (degenCK n m (j := j) l)) p := by
  have hfun : (fun p : Fin (degenDim n m j) → ℝ => degenC p l)
      = ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (degenDim n m j) => ℝ)
          (degenCK n m (j := j) l)) := rfl
  have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (degenDim n m j) => ℝ)
    (degenCK n m (j := j) l)).hasFDerivAt (x := p)
  rwa [← hfun] at this

/-- The derivative of the normalisation polynomial `∑ ν_a² - 1`. -/
def dgLam {j : ℕ} (p : Fin (degenDim n m j) → ℝ) : (Fin (degenDim n m j) → ℝ) →L[ℝ] ℝ :=
  ∑ a : Fin (j + 1), (2 * degenNu p a) •
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (degenDim n m j) => ℝ)
      (degenNuK n m (j := j) a))

theorem hasFDerivAt_lamFun {j : ℕ} (p : Fin (degenDim n m j) → ℝ) :
    HasFDerivAt (fun p' : Fin (degenDim n m j) → ℝ => (∑ a : Fin (j + 1), (degenNu p' a) ^ 2) - 1)
      (dgLam p) p := by
  have hterm : ∀ a : Fin (j + 1),
      HasFDerivAt (fun p' : Fin (degenDim n m j) → ℝ => (degenNu p' a) ^ 2)
        ((2 * degenNu p a) • (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin (degenDim n m j) => ℝ) (degenNuK n m (j := j) a))) p := by
    intro a
    have h := (hasFDerivAt_degenNu a p).mul (hasFDerivAt_degenNu a p)
    have hf : (fun p' : Fin (degenDim n m j) → ℝ => (degenNu p' a) ^ 2)
        = (fun p' => degenNu p' a) * (fun p' => degenNu p' a) := by
      funext x; rw [Pi.mul_apply]; ring
    have ha : (degenNu p a) • (ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Fin (degenDim n m j) => ℝ) (degenNuK n m (j := j) a))
          + (degenNu p a) • (ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Fin (degenDim n m j) => ℝ) (degenNuK n m (j := j) a))
        = (2 * degenNu p a) • (ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Fin (degenDim n m j) => ℝ) (degenNuK n m (j := j) a)) := by
      rw [two_mul, add_smul]
    rw [← hf, ha] at h
    exact h
  have hsum : HasFDerivAt (∑ a : Fin (j + 1), fun p' => (degenNu p' a) ^ 2)
      (∑ a : Fin (j + 1), (2 * degenNu p a) • (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (degenDim n m j) => ℝ) (degenNuK n m (j := j) a))) p :=
    HasFDerivAt.sum (u := Finset.univ) (fun a _ => hterm a)
  have hsub := hsum.sub (hasFDerivAt_const (1 : ℝ) p)
  have hf2 : (fun p' : Fin (degenDim n m j) → ℝ => (∑ a : Fin (j + 1), (degenNu p' a) ^ 2) - 1)
      = (∑ a : Fin (j + 1), fun p' => (degenNu p' a) ^ 2) - (fun _ => (1 : ℝ)) := by
    funext x; rw [Pi.sub_apply, Finset.sum_apply]
  have hd2 : (∑ a : Fin (j + 1), (2 * degenNu p a) • (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (degenDim n m j) => ℝ) (degenNuK n m (j := j) a))) - 0 = dgLam p := by
    rw [dgLam, sub_zero]
  rw [← hf2, hd2] at hsub
  exact hsub

/-- The `Φ c_l + ∂_l Φ`-value appearing in `degenPsi`. -/
def AVal (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (l : Fin (1 + m)) : ℝ :=
  eaEval S.X.c Phi (degenZ p) * degenC p l
    + eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) (degenZ p)

/-- The derivative of `AVal`. -/
def dgA (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (l : Fin (1 + m)) :
    (Fin (degenDim n m S.j) → ℝ) →L[ℝ] ℝ :=
  (eaEval S.X.c Phi (degenZ p)) • (ContinuousLinearMap.proj (degenCK n m (j := S.j) l))
    + (degenC p l) • (gradZ n m S.X.c Phi p)
    + gradZ n m S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) p

theorem hasFDerivAt_AVal (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (l : Fin (1 + m)) :
    HasFDerivAt (fun p => AVal S Phi p l) (dgA S Phi p l) p := by
  have h1 : HasFDerivAt (fun p : Fin (degenDim n m S.j) → ℝ =>
      eaEval S.X.c Phi (degenZ p) * degenC p l)
      ((eaEval S.X.c Phi (degenZ p)) • (ContinuousLinearMap.proj (degenCK n m (j := S.j) l))
        + (degenC p l) • (gradZ n m S.X.c Phi p)) p :=
    (hasFDerivAt_degenZ_eval S.X.c Phi p).mul (hasFDerivAt_degenC l p)
  have h2 := hasFDerivAt_degenZ_eval S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) p
  unfold AVal dgA
  exact h1.add h2

/-- The derivative of `degenPsi`. -/
def dgPsi (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (l : Fin (1 + m)) :
    (Fin (degenDim n m S.j) → ℝ) →L[ℝ] ℝ :=
  (degenNu p (Fin.last S.j)) • (dgA S Phi p l)
    + (AVal S Phi p l) • (ContinuousLinearMap.proj (degenNuK n m (j := S.j) (Fin.last S.j)))
    - ∑ a : Fin S.j,
        ((degenNu p (Fin.castAdd 1 a))
            • (gradZ n m S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) p)
          + (eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) (degenZ p))
              • (ContinuousLinearMap.proj (degenNuK n m (j := S.j) (Fin.castAdd 1 a))))

theorem hasFDerivAt_degenPsi (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (l : Fin (1 + m)) :
    HasFDerivAt (fun p => degenPsi S Phi p l) (dgPsi S Phi p l) p := by
  have h3 : HasFDerivAt
      (fun p : Fin (degenDim n m S.j) → ℝ => degenNu p (Fin.last S.j) * AVal S Phi p l)
      ((degenNu p (Fin.last S.j)) • (dgA S Phi p l)
        + (AVal S Phi p l) • (ContinuousLinearMap.proj
            (degenNuK n m (j := S.j) (Fin.last S.j)))) p :=
    (hasFDerivAt_degenNu (Fin.last S.j) p).mul (hasFDerivAt_AVal S Phi p l)
  have hterm4 : ∀ a : Fin S.j,
      HasFDerivAt (fun p' : Fin (degenDim n m S.j) → ℝ =>
          degenNu p' (Fin.castAdd 1 a)
            * eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) (degenZ p'))
        ((degenNu p (Fin.castAdd 1 a))
            • (gradZ n m S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) p)
          + (eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) (degenZ p))
              • (ContinuousLinearMap.proj
                  (degenNuK n m (j := S.j) (Fin.castAdd 1 a)))) p := by
    intro a
    exact (hasFDerivAt_degenNu (Fin.castAdd 1 a) p).mul
      (hasFDerivAt_degenZ_eval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) p)
  have h4' : HasFDerivAt
      (∑ a : Fin S.j, fun p' : Fin (degenDim n m S.j) → ℝ =>
          degenNu p' (Fin.castAdd 1 a)
            * eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) (degenZ p'))
      (∑ a : Fin S.j,
        ((degenNu p (Fin.castAdd 1 a))
            • (gradZ n m S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) p)
          + (eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) (degenZ p))
              • (ContinuousLinearMap.proj
                  (degenNuK n m (j := S.j) (Fin.castAdd 1 a))))) p :=
    HasFDerivAt.sum (u := Finset.univ) (fun a _ => hterm4 a)
  have h4 : HasFDerivAt
      (fun p : Fin (degenDim n m S.j) → ℝ => ∑ a : Fin S.j,
        degenNu p (Fin.castAdd 1 a)
          * eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) (degenZ p))
      (∑ a : Fin S.j,
        ((degenNu p (Fin.castAdd 1 a))
            • (gradZ n m S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) p)
          + (eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) (degenZ p))
              • (ContinuousLinearMap.proj
                  (degenNuK n m (j := S.j) (Fin.castAdd 1 a))))) p :=
    h4'.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext x; rw [Finset.sum_apply]))
  unfold degenPsi dgPsi
  exact h3.sub h4

/-- The `r`-th coordinate of the derivative of `degenH`. -/
def dgCoef (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (r : Fin (S.j + (1 + (1 + m)))) :
    (Fin (degenDim n m S.j) → ℝ) →L[ℝ] ℝ :=
  Fin.addCases
    (fun a : Fin S.j => gradZ n m S.X.c (S.h a) p)
    (fun s : Fin (1 + (1 + m)) =>
      Fin.addCases
        (fun _ : Fin 1 => dgLam p)
        (fun l : Fin (1 + m) => dgPsi S Phi p l) s)
    r

/-- The derivative of `degenH`. -/
def dgH (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) :
    (Fin (degenDim n m S.j) → ℝ) →L[ℝ] (Fin (S.j + (1 + (1 + m))) → ℝ) :=
  ContinuousLinearMap.pi (fun r => dgCoef S Phi p r)

theorem dgH_apply (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (v : Fin (degenDim n m S.j) → ℝ) (r) :
    dgH S Phi p v r = dgCoef S Phi p r v :=
  ContinuousLinearMap.pi_apply _ _ _

theorem hasFDerivAt_degenH (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) :
    HasFDerivAt (degenH S Phi) (dgH S Phi p) p := by
  rw [dgH]
  refine hasFDerivAt_pi.mpr (fun r => ?_)
  revert r
  refine Fin.addCases ?_ ?_
  · intro a
    have hcoef : dgCoef S Phi p (Fin.castAdd (1 + (1 + m)) a) = gradZ n m S.X.c (S.h a) p := by
      rw [dgCoef, Fin.addCases_left]
    have hfun : (fun p' : Fin (degenDim n m S.j) → ℝ =>
        degenH S Phi p' (Fin.castAdd (1 + (1 + m)) a))
        = fun p' => eaEval S.X.c (S.h a) (degenZ p') := by
      funext p'; simp only [degenH, Fin.append_left]
    rw [hfun, hcoef]
    exact hasFDerivAt_degenZ_eval S.X.c (S.h a) p
  · intro s
    revert s
    refine Fin.addCases ?_ ?_
    · intro u
      have hcoef : dgCoef S Phi p (Fin.natAdd S.j (Fin.castAdd (1 + m) u)) = dgLam p := by
        rw [dgCoef, Fin.addCases_right, Fin.addCases_left]
      have hfun : (fun p' : Fin (degenDim n m S.j) → ℝ =>
          degenH S Phi p' (Fin.natAdd S.j (Fin.castAdd (1 + m) u)))
          = fun p' => (∑ a : Fin (S.j + 1), (degenNu p' a) ^ 2) - 1 := by
        funext p'; simp only [degenH, Fin.append_left, Fin.append_right, degenLam]
      rw [hfun, hcoef]
      exact hasFDerivAt_lamFun p
    · intro l
      have hcoef : dgCoef S Phi p (Fin.natAdd S.j (Fin.natAdd 1 l)) = dgPsi S Phi p l := by
        rw [dgCoef, Fin.addCases_right, Fin.addCases_right]
      have hfun : (fun p' : Fin (degenDim n m S.j) → ℝ =>
          degenH S Phi p' (Fin.natAdd S.j (Fin.natAdd 1 l))) = fun p' => degenPsi S Phi p' l := by
        funext p'; simp only [degenH, Fin.append_left, Fin.append_right]
      rw [hfun, hcoef]
      exact hasFDerivAt_degenPsi S Phi p l

theorem fderiv_degenH (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) :
    fderiv ℝ (degenH S Phi) p = dgH S Phi p :=
  (hasFDerivAt_degenH S Phi p).fderiv

/-! ## §4. The derivative of `degenF` -/

/-- The (linear) map `degenF` itself: `p ↦ (projBase (degenZ p), degenC p)`. -/
def dgF (S : AmbStratum (n + (1 + m))) :
    (Fin (degenDim n m S.j) → ℝ) →L[ℝ] (Fin (n + (1 + m)) → ℝ) :=
  ContinuousLinearMap.pi (fun k : Fin (n + (1 + m)) =>
    Fin.addCases
      (fun i : Fin n =>
        ContinuousLinearMap.proj (degenZK n m (j := S.j) (Fin.castLE (Nat.le_add_right n (1 + m)) i)))
      (fun l : Fin (1 + m) => ContinuousLinearMap.proj (degenCK n m (j := S.j) l)) k)

theorem dgF_eq_degenF (S : AmbStratum (n + (1 + m))) (v : Fin (degenDim n m S.j) → ℝ) :
    dgF S v = degenF S v := by
  funext k
  revert k
  refine Fin.addCases ?_ ?_
  · intro i
    simp only [dgF, ContinuousLinearMap.pi_apply, Fin.addCases_left,
      ContinuousLinearMap.proj_apply, degenF, Fin.append_left, projBase, degenZ_apply_k]
  · intro l
    simp only [dgF, ContinuousLinearMap.pi_apply, Fin.addCases_right,
      ContinuousLinearMap.proj_apply, degenF, Fin.append_right, degenC_apply_k]

theorem hasFDerivAt_degenF (S : AmbStratum (n + (1 + m)))
    (p : Fin (degenDim n m S.j) → ℝ) :
    HasFDerivAt (degenF S) (dgF S) p := by
  have h := (dgF S).hasFDerivAt (x := p)
  have hfun : (degenF S) = ⇑(dgF S) := funext (fun v => (dgF_eq_degenF S v).symm)
  rw [hfun]
  exact h

theorem fderiv_degenF (S : AmbStratum (n + (1 + m)))
    (p : Fin (degenDim n m S.j) → ℝ) :
    fderiv ℝ (degenF S) p = dgF S :=
  (hasFDerivAt_degenF S p).fderiv

/-! ## §5. The embedding `emb` of the reduced variables -/

/-- The embedding of the reduced variables `(yt, ν)` into the ambient `(z,(ν,ν₀),c)`-space:
the `1+m` fibre coordinates of `z` and then the `j+1` multipliers. -/
def emb (n m : ℕ) {j : ℕ} (u : Fin ((1 + m) + (j + 1)) → ℝ) : Fin (degenDim n m j) → ℝ :=
  ∑ col, u col • Pi.single (degenColK n m (j := j) col) 1

theorem emb_apply_colK {j : ℕ} (u : Fin ((1 + m) + (j + 1)) → ℝ)
    (col : Fin ((1 + m) + (j + 1))) :
    emb n m u (degenColK n m (j := j) col) = u col := by
  have hsum : emb n m u (degenColK n m (j := j) col)
      = (∑ c, (u c • Pi.single (degenColK n m (j := j) c) 1)
          (degenColK n m (j := j) col)) := by
    rw [emb, Finset.sum_apply]
  rw [hsum]
  have key : (∑ c, (u c • Pi.single (degenColK n m (j := j) c) 1)
          (degenColK n m (j := j) col))
      = (u col • Pi.single (degenColK n m (j := j) col) 1)
          (degenColK n m (j := j) col) :=
    Finset.sum_eq_single col
      (fun c _ hc => by
        rw [Pi.smul_apply,
          Pi.single_eq_of_ne (i := degenColK n m (j := j) c)
            (i' := degenColK n m (j := j) col)
            (fun hh => hc (degenColK_injective hh).symm),
          smul_eq_mul, mul_zero])
      (fun h => absurd (Finset.mem_univ col) h)
  rw [key, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]

theorem emb_zero {j : ℕ} :
    emb n m (0 : Fin ((1 + m) + (j + 1)) → ℝ) = (0 : Fin (degenDim n m j) → ℝ) := by
  funext k
  rw [emb, Finset.sum_apply]
  refine Finset.sum_eq_zero (fun c _ => ?_)
  simp

theorem emb_injective {j : ℕ} : Function.Injective (emb n m (j := j)) := by
  intro u v h
  funext col
  have h2 := congrFun h (degenColK n m (j := j) col)
  rw [emb_apply_colK u col, emb_apply_colK v col] at h2
  exact h2

theorem emb_apply_of_lt {j : ℕ} (u : Fin ((1 + m) + (j + 1)) → ℝ) (k : Fin (degenDim n m j))
    (hk : k.val < n) : emb n m u k = 0 := by
  rw [emb, Finset.sum_apply]
  refine Finset.sum_eq_zero (fun c _ => ?_)
  rw [Pi.smul_apply, Pi.single_eq_of_ne (fun hh => ?_), smul_eq_mul, mul_zero]
  have := degenColK_val_ge (n := n) (m := m) (j := j) c
  rw [← hh] at this
  omega

theorem emb_apply_of_ge {j : ℕ} (u : Fin ((1 + m) + (j + 1)) → ℝ) (k : Fin (degenDim n m j))
    (hk : n + (1 + m) + (j + 1) ≤ k.val) : emb n m u k = 0 := by
  rw [emb, Finset.sum_apply]
  refine Finset.sum_eq_zero (fun c _ => ?_)
  rw [Pi.smul_apply, Pi.single_eq_of_ne (fun hh => ?_), smul_eq_mul, mul_zero]
  have := degenColK_val_lt (n := n) (m := m) (j := j) c
  rw [← hh] at this
  omega

/-- A vector supported on the `(yt,ν)`-coordinates is `emb` of its restriction. -/
theorem eq_emb_of_supported {j : ℕ} (v : Fin (degenDim n m j) → ℝ)
    (hx : ∀ i : Fin n,
      v (degenZK n m (j := j) (Fin.castLE (Nat.le_add_right n (1 + m)) i)) = 0)
    (hc : ∀ l : Fin (1 + m), v (degenCK n m (j := j) l) = 0) :
    v = emb n m (fun col => v (degenColK n m (j := j) col)) := by
  funext k
  obtain ⟨kv, hkv⟩ := k
  have hkvb : kv < n + (1 + m) + (j + 1) + (1 + m) := by simpa only [degenDim] using hkv
  rcases lt_or_ge kv n with h1 | h1
  · have hk : v ⟨kv, hkv⟩ = 0 := by
      have := hx ⟨kv, h1⟩
      rwa [show (degenZK n m (j := j) (Fin.castLE (Nat.le_add_right n (1 + m)) ⟨kv, h1⟩))
          = (⟨kv, hkv⟩ : Fin (degenDim n m j)) from Fin.ext rfl] at this
    rw [hk, emb_apply_of_lt (fun col => v (degenColK n m (j := j) col)) ⟨kv, hkv⟩ h1]
  · rcases lt_or_ge kv (n + (1 + m)) with h2 | h2
    · have hk : (⟨kv, hkv⟩ : Fin (degenDim n m j))
          = degenZK n m (j := j) (Fin.natAdd n ⟨kv - n, by omega⟩) :=
        Fin.ext (by simp only [degenZK_val, Fin.val_natAdd, Fin.val_mk]; omega)
      rw [hk, ← degenColK_castAdd (n := n) (m := m) (j := j) (⟨kv - n, by omega⟩ : Fin (1 + m))]
      rw [emb_apply_colK]
    · rcases lt_or_ge kv (n + (1 + m) + (j + 1)) with h3 | h3
      · have hk : (⟨kv, hkv⟩ : Fin (degenDim n m j))
            = degenNuK n m (j := j) (⟨kv - (n + (1 + m)), by omega⟩ : Fin (j + 1)) :=
          Fin.ext (by simp only [degenNuK_val, Fin.val_mk]; omega)
        rw [hk, ← degenColK_natAdd (n := n) (m := m) (j := j)
          (⟨kv - (n + (1 + m)), by omega⟩ : Fin (j + 1))]
        rw [emb_apply_colK]
      · have hge := emb_apply_of_ge (fun col => v (degenColK n m (j := j) col)) ⟨kv, hkv⟩ h3
        have hk : (⟨kv, hkv⟩ : Fin (degenDim n m j))
            = degenCK n m (j := j) (⟨kv - (n + (1 + m) + (j + 1)), by omega⟩ : Fin (1 + m)) :=
          Fin.ext (by simp only [degenCK_val, Fin.val_mk]; omega)
        rw [hk] at hge
        rw [hk, hc (⟨kv - (n + (1 + m) + (j + 1)), by omega⟩ : Fin (1 + m)), hge]

/-- The equation index transfer `degenRowInv` is surjective. -/
theorem degenRowInv_surjective {j : ℕ} :
    Function.Surjective (degenRowInv m (j := j) :
      Fin ((1 + m) + (j + 1)) → Fin (j + (1 + (1 + m)))) := by
  intro r
  obtain ⟨rv, hrv⟩ := r
  rcases lt_or_ge rv j with h1 | h1
  · refine ⟨Fin.natAdd (1 + m) (Fin.castAdd 1 ⟨rv, h1⟩), ?_⟩
    rw [degenRowInv, Fin.addCases_right, Fin.addCases_left]
    exact Fin.ext (by simp)
  · rcases lt_or_ge rv (j + 1) with h2 | h2
    · refine ⟨Fin.natAdd (1 + m) (Fin.last j), ?_⟩
      rw [degenRowInv, Fin.addCases_right]
      rw [show (Fin.last j : Fin (j + 1)) = Fin.natAdd j (0 : Fin 1) from Fin.ext (by simp),
        Fin.addCases_right]
      exact Fin.ext (by simp only [Fin.val_natAdd, Fin.val_castAdd]; omega)
    · refine ⟨Fin.castAdd (j + 1) ⟨rv - (j + 1), by omega⟩, ?_⟩
      rw [degenRowInv, Fin.addCases_left]
      exact Fin.ext (by simp only [Fin.val_natAdd]; omega)

end Work.WilE9G.Lagrange
