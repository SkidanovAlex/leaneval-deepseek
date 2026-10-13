/-
  Area G4b: the bad set `badSet f s` of `G4_bdd_dx` is an `Ω`-set.

  For `f : ℝ^{m+1} → ℝ` with `Ω`-definable graph and `s : Finset ℝ`,
  `badSet f s = {x ∈ (0,1) \ s : ∂₀ f is unbounded on the fibre over x}` — see `Basic.lean`.
  We show that it is `Ω`-definable with format `F + K` and degree a polynomial in `D`.

  The proof is a calculation in the frozen `Ω`-calculus, in the ambient space
  `ℝ^{2 + (m+1)}` with coordinates `(M, x, y, t)`:

  * `derivBlock f` is the pullback of the derivative graph `derivGraph f 0` (which `SharpDeriv`
    exhibits as an `Ω`-set) along the index map `gZ : Fin (m+2) → Fin (2+(m+1))` inserting the
    free coordinate `M`, i.e. the set of `(M,x,y,t)` with `(x,y) ∈ c1Loc f` and `t = ∂₀ f (x,y)`;
  * `cubeBlock m` is the pullback of `openCube m` along `gY`, and `absBlock m` is the set
    `{M < |t|}`, manufactured from `posPoly_mem`;
  * `BIG f` is their intersection; `Work.WilG5.projN (m+1)` existentially quantifies the
    `(y,t)`-block, so `v ∈ projN (m+1) (BIG f)` iff, with `x = v 1` and `M = v 0`, there are
    `y ∈ openCube m` and `t = ∂₀ f (x,y)` with `(x,y) ∈ c1Loc f` and `M < |t|`;
  * the universal quantification over `M` is performed by complementing, taking the coordinate
    image along `gE1 : Fin 1 → Fin 2` (which reads the `x`-coordinate) and complementing again.
    The result is `badCore f = {x : ∂₀ f unbounded over the fibre over x}`;
  * finally `badSet f s = ((badCore f) ∩ {x 0 ∈ (0,1)}) ∩ {x 0 ∉ s}`, and each of the two
    elementary sets is an `Ω`-set of dimension one.
-/
import Mathlib
import Submission.Work.WilG4b.Basic
import Submission.Work.WilG4b.posPoly_mem
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG1.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilG4b

open WilkiesDesign WilkiesConjecture

/-! ## 0. The derivative graph of `SharpDeriv` at order one -/

/-- The order-one iterated derivative, evaluated on a direction, is the Fréchet derivative. -/
theorem iteratedFDeriv_one_apply {n : ℕ} (f : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ)
    (v : Fin n → ℝ) :
    iteratedFDeriv ℝ 1 f y (fun _ : Fin 1 => v) = fderiv ℝ f y v := by
  have h := iteratedFDerivWithin_one_apply (𝕜 := ℝ) (s := Set.univ) (f := f) (x := y)
    uniqueDiffWithinAt_univ (fun _ : Fin 1 => v)
  rw [iteratedFDerivWithin_univ, fderivWithin_univ] at h
  simpa using h

/-- The set appearing in `SOMin.SharpDeriv` at order one is the derivative graph. -/
theorem sharp_eq_derivGraph {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n) :
    {z : Fin (n + 1) → ℝ |
        Fin.init z ∈ interior {x : Fin n → ℝ | ContDiffAt ℝ (1 : ℕ) f x} ∧
        z (Fin.last n) =
          iteratedFDeriv ℝ 1 f (Fin.init z) (fun _ : Fin 1 => Pi.single i 1)}
      = derivGraph f i := by
  ext z
  simp only [derivGraph, c1Loc, dDir]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2]; exact iteratedFDeriv_one_apply f (Fin.init z) (Pi.single i 1)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2]; exact (iteratedFDeriv_one_apply f (Fin.init z) (Pi.single i 1)).symm⟩

/-- **Sharp derivatives at order one.**  `SharpDeriv` exhibits the derivative graph of `∂ᵢ f`
as an `Ω`-set, with format depending only on the input format and degree a polynomial in the
input degree (with the second variable fixed to `1`). -/
theorem derivGraph_mem (S : SOMin) (hder : S.SharpDeriv) (m F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (f : (Fin m → ℝ) → ℝ) (i : Fin m),
        graphOf f ∈ S.Ω F0 D (m + 1) →
          derivGraph f i ∈ S.Ω a (MvPolynomial.eval ![D, 1] b) (m + 1) := by
  obtain ⟨a, b, hb⟩ := hder F0 m
  refine ⟨a, b, fun D f i hf => ?_⟩
  have h := hb D f hf 1 (fun _ : Fin 1 => i)
  rw [sharp_eq_derivGraph f i] at h
  exact h

/-! ## 1. Coordinates of the ambient space `ℝ^{2 + (m+1)} = (M, x, y, t)` -/

/-- The coordinate of the threshold `M`. -/
def gM (m : ℕ) : Fin (2 + (m + 1)) := ⟨0, by omega⟩

/-- The coordinate of `x`. -/
def gX (m : ℕ) : Fin (2 + (m + 1)) := ⟨1, by omega⟩

/-- The coordinate of `y j`. -/
def gY (m : ℕ) (j : Fin m) : Fin (2 + (m + 1)) := ⟨j.val + 2, by omega⟩

/-- The coordinate of `t = ∂₀ f`. -/
def gT (m : ℕ) : Fin (2 + (m + 1)) := ⟨m + 2, by omega⟩

/-- The coordinate of the `i`-th entry of the `(x,y)`-block. -/
def gXY (m : ℕ) (i : Fin (m + 1)) : Fin (2 + (m + 1)) := ⟨i.val + 1, by omega⟩

/-- The index map inserting the free coordinate `M`: the coordinates of the derivative graph
in the ambient space. -/
def gZ (m : ℕ) (k : Fin (m + 2)) : Fin (2 + (m + 1)) := ⟨k.val + 1, by omega⟩

/-- The coordinate map keeping only the `x`-coordinate of the pair `(M,x)`. -/
def gE1 : Fin 1 → Fin 2 := fun _ => 1

@[simp] theorem gM_val (m : ℕ) : (gM m).val = 0 := rfl

@[simp] theorem gX_val (m : ℕ) : (gX m).val = 1 := rfl

@[simp] theorem gY_val (m : ℕ) (j : Fin m) : (gY m j).val = j.val + 2 := rfl

@[simp] theorem gT_val (m : ℕ) : (gT m).val = m + 2 := rfl

@[simp] theorem gXY_val (m : ℕ) (i : Fin (m + 1)) : (gXY m i).val = i.val + 1 := rfl

@[simp] theorem gZ_val (m : ℕ) (k : Fin (m + 2)) : (gZ m k).val = k.val + 1 := rfl

theorem gM_eq_castAdd (m : ℕ) : gM m = Fin.castAdd (m + 1) (0 : Fin 2) := Fin.ext rfl

theorem gX_eq_castAdd (m : ℕ) : gX m = Fin.castAdd (m + 1) (1 : Fin 2) := Fin.ext rfl

theorem gY_eq_natAdd (m : ℕ) (j : Fin m) : gY m j = Fin.natAdd 2 j.castSucc :=
  Fin.ext (Nat.add_comm j.val 2)

theorem gT_eq_natAdd (m : ℕ) : gT m = Fin.natAdd 2 (Fin.last m) :=
  Fin.ext (Nat.add_comm m 2)

theorem gXY_zero (m : ℕ) : gXY m 0 = gX m := Fin.ext rfl

theorem gXY_succ (m : ℕ) (j : Fin m) : gXY m (Fin.succ j) = gY m j := Fin.ext rfl

theorem gZ_castSucc (m : ℕ) (i : Fin (m + 1)) : gZ m i.castSucc = gXY m i := Fin.ext rfl

theorem gZ_last (m : ℕ) : gZ m (Fin.last (m + 1)) = gT m := Fin.ext rfl

/-- The `(x,y)`-block of a point of the ambient space, read through `gZ`. -/
theorem cons_gXY (m : ℕ) (w : Fin (2 + (m + 1)) → ℝ) :
    Fin.cons (w (gX m)) (fun j : Fin m => w (gY m j))
      = fun i : Fin (m + 1) => w (gXY m i) := by
  funext i
  induction i using Fin.cases with
  | zero => rw [Fin.cons_zero]; exact congrArg w (gXY_zero m).symm
  | succ j => rw [Fin.cons_succ]; exact congrArg w (gXY_succ m j).symm

/-! ## 2. The blocks of the ambient space -/

/-- The pullback of the derivative graph: `(x,y) ∈ c1Loc f` and `t = ∂₀ f (x,y)`. -/
def derivBlock {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℝ) : Set (Fin (2 + (m + 1)) → ℝ) :=
  Work.WilG5.coordPre (gZ m) (derivGraph f (0 : Fin (m + 1)))

/-- The `y`-block lies in the open cube. -/
def cubeBlock (m : ℕ) : Set (Fin (2 + (m + 1)) → ℝ) :=
  Work.WilG5.coordPre (gY m) (openCube m)

/-- The inequality `M < |t|` (respectively `M < |∂₀ f|` after projecting). -/
def absBlock (m : ℕ) : Set (Fin (2 + (m + 1)) → ℝ) :=
  {w | w (gM m) < |w (gT m)|}

/-- The joint set. -/
def BIG {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℝ) : Set (Fin (2 + (m + 1)) → ℝ) :=
  derivBlock f ∩ (cubeBlock m ∩ absBlock m)

theorem mem_derivBlock {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℝ) (w : Fin (2 + (m + 1)) → ℝ) :
    w ∈ derivBlock f ↔
      (fun i : Fin (m + 1) => w (gXY m i)) ∈ c1Loc f ∧
        w (gT m) = dDir f (0 : Fin (m + 1)) (fun i : Fin (m + 1) => w (gXY m i)) := by
  have hinit : Fin.init (w ∘ gZ m) = fun i : Fin (m + 1) => w (gXY m i) := by
    funext i
    show w (gZ m i.castSucc) = w (gXY m i)
    rw [gZ_castSucc]
  have hlast : (w ∘ gZ m) (Fin.last (m + 1)) = w (gT m) := by
    show w (gZ m (Fin.last (m + 1))) = w (gT m)
    rw [gZ_last]
  have hmem : w ∈ derivBlock f ↔
      Fin.init (w ∘ gZ m) ∈ c1Loc f ∧
        (w ∘ gZ m) (Fin.last (m + 1)) = dDir f 0 (Fin.init (w ∘ gZ m)) := Iff.rfl
  rw [hmem, hinit, hlast]

theorem mem_cubeBlock {m : ℕ} (w : Fin (2 + (m + 1)) → ℝ) :
    w ∈ cubeBlock m ↔ ∀ j : Fin m, w (gY m j) ∈ Set.Ioo (0 : ℝ) 1 := Iff.rfl

/-- Membership in `BIG`, in terms of the data `(M, x, y, t)`. -/
theorem mem_BIG_iff {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℝ) (w : Fin (2 + (m + 1)) → ℝ) :
    w ∈ BIG f ↔
      (Fin.cons (w (gX m)) (fun j : Fin m => w (gY m j)) ∈ c1Loc f ∧
        w (gT m) = dDir f (0 : Fin (m + 1))
          (Fin.cons (w (gX m)) (fun j : Fin m => w (gY m j))) ∧
        (∀ j : Fin m, w (gY m j) ∈ Set.Ioo (0 : ℝ) 1) ∧
        w (gM m) < |w (gT m)|) := by
  rw [BIG, Set.mem_inter_iff, Set.mem_inter_iff, mem_derivBlock, mem_cubeBlock]
  have ha : w ∈ absBlock m ↔ w (gM m) < |w (gT m)| := Iff.rfl
  rw [ha, ← cons_gXY m w]
  tauto

theorem append_gM {m : ℕ} (v : Fin 2 → ℝ) (u : Fin (m + 1) → ℝ) :
    (Fin.append v u) (gM m) = v 0 := by
  rw [gM_eq_castAdd, Fin.append_left]

theorem append_gX {m : ℕ} (v : Fin 2 → ℝ) (u : Fin (m + 1) → ℝ) :
    (Fin.append v u) (gX m) = v 1 := by
  rw [gX_eq_castAdd, Fin.append_left]

theorem append_gY {m : ℕ} (v : Fin 2 → ℝ) (u : Fin (m + 1) → ℝ) (j : Fin m) :
    (Fin.append v u) (gY m j) = u j.castSucc := by
  rw [gY_eq_natAdd, Fin.append_right]

theorem append_gT {m : ℕ} (v : Fin 2 → ℝ) (u : Fin (m + 1) → ℝ) :
    (Fin.append v u) (gT m) = u (Fin.last m) := by
  rw [gT_eq_natAdd, Fin.append_right]

/-- Membership in the projection of `BIG`, in terms of the pair `(M, x)`. -/
theorem mem_projN_BIG_iff {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℝ) (v : Fin 2 → ℝ) :
    v ∈ Work.WilG5.projN (m + 1) (BIG f) ↔
      ∃ (y : Fin m → ℝ) (t : ℝ),
        Fin.cons (v 1) y ∈ c1Loc f ∧ t = dDir f (0 : Fin (m + 1)) (Fin.cons (v 1) y) ∧
          (∀ j : Fin m, y j ∈ Set.Ioo (0 : ℝ) 1) ∧ v 0 < |t| := by
  constructor
  · rw [Work.WilG5.projN, Set.mem_ofPred_eq]
    rintro ⟨u, hu⟩
    rw [mem_BIG_iff] at hu
    simp only [append_gX, append_gY, append_gT, append_gM] at hu
    exact ⟨fun j => u j.castSucc, u (Fin.last m), hu.1, hu.2.1, hu.2.2.1, hu.2.2.2⟩
  · rintro ⟨y, t, h1, h2, h3, h4⟩
    rw [Work.WilG5.projN, Set.mem_ofPred_eq]
    refine ⟨Fin.snoc y t, ?_⟩
    rw [mem_BIG_iff]
    simp only [append_gX, append_gY, append_gT, append_gM]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    exact ⟨h1, h2, h3, h4⟩

/-! ## 3. The bad core is the complement of a coordinate image -/

/-- The universal quantification over `M` is the complement of a coordinate image. -/
theorem badCore_eq {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℝ) :
    (Work.WilG5.coordImage gE1 (Work.WilG5.projN (m + 1) (BIG f))ᶜ)ᶜ = badCore f := by
  ext x
  have key : ∀ w : Fin 2 → ℝ, w ∘ gE1 = x ↔ w 1 = x 0 := by
    intro w
    constructor
    · intro h
      have h0 := congrFun h 0
      simpa [gE1] using h0
    · intro h
      funext i
      fin_cases i
      simp [gE1, h]
  have hL : x ∈ (Work.WilG5.coordImage gE1 (Work.WilG5.projN (m + 1) (BIG f))ᶜ)ᶜ ↔
      ∀ w : Fin 2 → ℝ, w ∘ gE1 = x → w ∈ Work.WilG5.projN (m + 1) (BIG f) := by
    rw [Set.mem_compl_iff, Work.WilG5.coordImage, Set.mem_ofPred_eq]
    constructor
    · intro h w hw
      by_contra hcon
      exact h ⟨w, hcon, hw⟩
    · rintro h ⟨w, hw, hwx⟩
      exact hw (h w hwx)
  rw [hL]
  constructor
  · intro h
    rw [badCore_iff]
    intro M
    have hw : pair M (x 0) ∈ Work.WilG5.projN (m + 1) (BIG f) :=
      h (pair M (x 0)) ((key (pair M (x 0))).mpr (by simp))
    rw [mem_projN_BIG_iff] at hw
    obtain ⟨y, t, hc, ht, hcube, hlt⟩ := hw
    subst ht
    simp only [pair_zero, pair_one] at hc hlt
    exact ⟨y, fun j => hcube j, hc, hlt⟩
  · intro hx w hweq
    have hw1 : w 1 = x 0 := (key w).mp hweq
    rw [badCore_iff] at hx
    obtain ⟨y, hcube, hc, hbd⟩ := hx (w 0)
    rw [mem_projN_BIG_iff]
    refine ⟨y, dDir f (0 : Fin (m + 1)) (Fin.cons (w 1) y), ?_, rfl, fun j => hcube j, ?_⟩
    · rw [hw1]; exact hc
    · rw [hw1]; exact hbd

/-- `badSet` is the intersection of `badCore` with the two elementary conditions. -/
theorem badSet_eq {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℝ) (s : Finset ℝ) :
    badSet f s =
      (badCore f ∩ {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo (0 : ℝ) 1})
        ∩ {x : Fin 1 → ℝ | x 0 ∉ (s : Set ℝ)} := by
  ext x
  simp only [badSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

/-! ## 4. The elementary `Ω`-sets -/

/-- The inequality `M < |t|` in the ambient space is an `Ω`-set. -/
theorem absBlock_mem (S : SOMin) (m : ℕ) :
    absBlock m ∈ S.Ω ((2 + (m + 1)) + 4) 8 (2 + (m + 1)) := by
  have htd1 : (MvPolynomial.X (gT m) - MvPolynomial.X (gM m) :
      MvPolynomial (Fin (2 + (m + 1))) ℝ).totalDegree ≤ 1 :=
    le_trans (Work.WilG5.td_sub_le _ _) (max_le (Work.WilG5.td_X_le _) (Work.WilG5.td_X_le _))
  have htd2 : (MvPolynomial.C (-1) * MvPolynomial.X (gT m) - MvPolynomial.X (gM m) :
      MvPolynomial (Fin (2 + (m + 1))) ℝ).totalDegree ≤ 1 := by
    refine le_trans (Work.WilG5.td_sub_le _ _) (max_le ?_ (Work.WilG5.td_X_le _))
    refine le_trans (Work.WilG5.td_mul_le _ _) ?_
    have h1 : ((MvPolynomial.C (-1) : MvPolynomial (Fin (2 + (m + 1))) ℝ)).totalDegree ≤ 0 :=
      Work.WilG5.td_C_le (-1 : ℝ)
    have h2 : ((MvPolynomial.X (gT m) : MvPolynomial (Fin (2 + (m + 1))) ℝ)).totalDegree ≤ 1 :=
      Work.WilG5.td_X_le (gT m)
    omega
  have h1 : {w : Fin (2 + (m + 1)) → ℝ | 0 < MvPolynomial.eval w
      (MvPolynomial.X (gT m) - MvPolynomial.X (gM m) : MvPolynomial (Fin (2 + (m + 1))) ℝ)}
      ∈ S.Ω ((2 + (m + 1)) + 4) 4 (2 + (m + 1)) :=
    Work.WilG5.mem_mono
      (posPoly_mem S (MvPolynomial.X (gT m) - MvPolynomial.X (gM m) :
        MvPolynomial (Fin (2 + (m + 1))) ℝ))
      ((2 + (m + 1)) + 4) 4 le_rfl (by omega)
  have h2 : {w : Fin (2 + (m + 1)) → ℝ | 0 < MvPolynomial.eval w
      (MvPolynomial.C (-1) * MvPolynomial.X (gT m) - MvPolynomial.X (gM m) :
        MvPolynomial (Fin (2 + (m + 1))) ℝ)}
      ∈ S.Ω ((2 + (m + 1)) + 4) 4 (2 + (m + 1)) :=
    Work.WilG5.mem_mono
      (posPoly_mem S (MvPolynomial.C (-1) * MvPolynomial.X (gT m) - MvPolynomial.X (gM m) :
        MvPolynomial (Fin (2 + (m + 1))) ℝ))
      ((2 + (m + 1)) + 4) 4 le_rfl (by omega)
  have h := S.union (F := (2 + (m + 1)) + 4) (fun _ : Fin 2 => 4)
    (fun i : Fin 2 => if i = 0
      then {w : Fin (2 + (m + 1)) → ℝ | 0 < MvPolynomial.eval w
        (MvPolynomial.X (gT m) - MvPolynomial.X (gM m) :
          MvPolynomial (Fin (2 + (m + 1))) ℝ)}
      else {w : Fin (2 + (m + 1)) → ℝ | 0 < MvPolynomial.eval w
        (MvPolynomial.C (-1) * MvPolynomial.X (gT m) - MvPolynomial.X (gM m) :
          MvPolynomial (Fin (2 + (m + 1))) ℝ)})
    (by intro i
        fin_cases i
        · simpa using h1
        · simpa using h2)
  rw [show (∑ _ : Fin 2, (4 : ℕ)) = 8 from by simp] at h
  rw [Work.WilG1.Omega.iUnion_fin_two] at h
  have hset : ({w : Fin (2 + (m + 1)) → ℝ | 0 < MvPolynomial.eval w
        (MvPolynomial.X (gT m) - MvPolynomial.X (gM m) :
          MvPolynomial (Fin (2 + (m + 1))) ℝ)} ∪
      {w : Fin (2 + (m + 1)) → ℝ | 0 < MvPolynomial.eval w
        (MvPolynomial.C (-1) * MvPolynomial.X (gT m) - MvPolynomial.X (gM m) :
          MvPolynomial (Fin (2 + (m + 1))) ℝ)}) = absBlock m := by
    ext w
    simp only [Set.mem_union, Set.mem_ofPred_eq, absBlock, MvPolynomial.eval_sub,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    rw [lt_abs]
    constructor
    · rintro (h | h)
      · left; linarith
      · right; linarith
    · rintro (h | h)
      · left; linarith
      · right; linarith
  rwa [hset] at h

/-- The interval `(0,1)` in dimension one. -/
theorem interval_mem (S : SOMin) (D : ℕ) :
    {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo (0 : ℝ) 1}
      ∈ S.Ω 25 (Polynomial.eval D (Polynomial.C 16)) 1 := by
  have h1 : {x : Fin 1 → ℝ | 0 < x 0} ∈ S.Ω 24 ((Polynomial.C 8).eval D) 1 := by
    simpa using (Work.WilG5.ltSet_mem (S := S) (n := 1) (0 : Fin 1) 0)
  have h2 : {x : Fin 1 → ℝ | x 0 < 1} ∈ S.Ω 24 ((Polynomial.C 8).eval D) 1 := by
    simpa using (Work.WilG5.gtSet_mem (S := S) (n := 1) (0 : Fin 1) 1)
  have h := S.inter (F := 24) (fun _ : Fin 2 => 8)
    (fun i : Fin 2 => if i = 0 then {x : Fin 1 → ℝ | 0 < x 0}
      else {x : Fin 1 → ℝ | x 0 < 1})
    (by intro i
        fin_cases i
        · simpa using h1
        · simpa using h2)
  rw [show (∑ _ : Fin 2, (8 : ℕ)) = 16 from by simp] at h
  rw [Work.WilG1.Omega.iInter_fin_two] at h
  have he : {x : Fin 1 → ℝ | 0 < x 0} ∩ {x : Fin 1 → ℝ | x 0 < 1}
      = {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo (0 : ℝ) 1} := by
    ext x
    simp [Set.mem_Ioo]
  rw [he] at h
  refine Work.WilG5.mem_mono h 25 (Polynomial.eval D (Polynomial.C 16)) ?_ ?_
  · omega
  · simp

/-- The complement of a finite set of reals, in dimension one. -/
theorem notMem_mem (S : SOMin) (s : Finset ℝ) (D : ℕ) :
    {x : Fin 1 → ℝ | x 0 ∉ (s : Set ℝ)}
      ∈ S.Ω (s.card + 6) (Polynomial.eval D (Polynomial.C (s.card + 4))) 1 := by
  induction s using Finset.induction with
  | empty =>
      have h : {x : Fin 1 → ℝ | x 0 ∉ ((∅ : Finset ℝ) : Set ℝ)} = Set.univ := by
        ext x; simp
      rw [h]
      have hu := Work.WilG5.univ_mem (S := S) (n := 1)
      refine Work.WilG5.mem_mono hu ((∅ : Finset ℝ).card + 6)
        (Polynomial.eval D (Polynomial.C ((∅ : Finset ℝ).card + 4))) ?_ ?_
      · simp
      · simp
  | insert t s' ht ih =>
      have hcard : (insert t s').card = s'.card + 1 := Finset.card_insert_of_notMem ht
      have hset : {x : Fin 1 → ℝ | x 0 ∉ ((insert t s' : Finset ℝ) : Set ℝ)}
          = {x : Fin 1 → ℝ | x 0 ≠ t}
            ∩ {x : Fin 1 → ℝ | x 0 ∉ ((s' : Finset ℝ) : Set ℝ)} := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Finset.mem_coe, Finset.mem_insert]
        constructor
        · intro h
          exact ⟨fun hx => h (Or.inl hx), fun hx => h (Or.inr hx)⟩
        · rintro ⟨h1, h2⟩ (hx | hx)
          · exact h1 hx
          · exact h2 hx
      rw [hset]
      have hH : {x : Fin 1 → ℝ | x 0 = t} ∈ S.Ω 1 ((Polynomial.C 1).eval D) 1 := by
        have hP : (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C t :
            MvPolynomial (Fin 1) ℝ).totalDegree ≤ 1 := by
          refine le_trans (Work.WilG5.td_sub_le _ _) (max_le ?_ ?_)
          · simp [MvPolynomial.totalDegree_X]
          · exact le_trans (Work.WilG5.td_C_le t) (Nat.zero_le 1)
        have h := S.hyp 1 (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C t :
          MvPolynomial (Fin 1) ℝ)
        have he : {x : Fin 1 → ℝ | MvPolynomial.eval x
              (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C t : MvPolynomial (Fin 1) ℝ) = 0}
            = {x : Fin 1 → ℝ | x 0 = t} := by
          ext x
          simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
            MvPolynomial.eval_C, sub_eq_zero]
        rw [he] at h
        refine Work.WilG1.Omega.mono h le_rfl ?_
        simpa using hP
      have hHN : {x : Fin 1 → ℝ | x 0 ≠ t} ∈ S.Ω 2 ((Polynomial.C 1).eval D) 1 := by
        have h := S.compl hH
        have he : ({x : Fin 1 → ℝ | x 0 = t})ᶜ = {x : Fin 1 → ℝ | x 0 ≠ t} := by
          ext x; simp
        rwa [he] at h
      have h := S.inter (F := max 2 (s'.card + 6))
        (fun i : Fin 2 => if i = 0 then (Polynomial.C 1).eval D
          else Polynomial.eval D (Polynomial.C (s'.card + 4)))
        (fun i : Fin 2 => if i = 0 then {x : Fin 1 → ℝ | x 0 ≠ t}
          else {x : Fin 1 → ℝ | x 0 ∉ ((s' : Finset ℝ) : Set ℝ)})
        (by intro i
            fin_cases i
            · exact Work.WilG1.Omega.mono hHN (le_max_left 2 (s'.card + 6)) le_rfl
            · exact Work.WilG1.Omega.mono ih (le_max_right 2 (s'.card + 6)) le_rfl)
      rw [show (∑ i : Fin 2, (if i = 0 then (Polynomial.C 1).eval D
            else Polynomial.eval D (Polynomial.C (s'.card + 4))))
          = (Polynomial.C 1 + Polynomial.C (s'.card + 4)).eval D from by
        rw [Fin.sum_univ_two]; simp [Polynomial.eval_add]] at h
      rw [Work.WilG1.Omega.iInter_fin_two] at h
      refine Work.WilG5.mem_mono h ((insert t s').card + 6)
        (Polynomial.eval D (Polynomial.C ((insert t s').card + 4))) ?_ ?_
      · have hm : max 2 (s'.card + 6) ≤ s'.card + 6 := max_le (by omega) le_rfl
        rw [hcard]
        omega
      · rw [hcard]
        simp only [Polynomial.eval_add, Polynomial.eval_C]
        omega

/-! ## 5. The main theorem -/

theorem badSet_mem (S : WilkiesDesign.SOMin) (hder : S.SharpDeriv) {m : ℕ} (s : Finset ℝ) :
    ∀ F : ℕ, ∃ (K : ℕ) (p : Polynomial ℕ), ∀ (D : ℕ) (f : (Fin (m + 1) → ℝ) → ℝ),
      WilkiesDesign.graphOf f ∈ S.Ω F D (m + 2) →
        Work.WilG4b.badSet f s ∈ S.Ω (F + K) (p.eval D) 1 := by
  intro F
  obtain ⟨a, b, hb⟩ := derivGraph_mem S hder (m + 1) F
  let cA : ℕ := 64 * ((2 + (m + 1)) + (m + 2)) + 64
  let eA : ℕ := 32 * ((2 + (m + 1)) + (m + 2)) + 32
  let cC : ℕ := 64 * ((2 + (m + 1)) + m) + 64
  let eC : ℕ := 32 * ((2 + (m + 1)) + m) + 32
  let Fg : ℕ := a + 1000 * (m + 1) + 1000 * s.card + 1000
  let Fg2 : ℕ := Fg + 2 + (m + 1) + 257 + 25 + (s.card + 6) + 100
  let cc : ℕ := eA + (16 * m + 16) + eC + 8 + 128 + 16 + (s.card + 4)
  refine ⟨Fg2 + 2, Work.WilG1.psubst b 1 + Polynomial.C cc, ?_⟩
  intro D f hf
  let bd : ℕ := MvPolynomial.eval ![D, 1] b
  let qA : ℕ := bd + eA
  let qC : ℕ := (16 * m + 16) + eC
  let qBIG : ℕ := qA + (qC + 8)
  let qI : ℕ := qBIG + 32 * (2 + 1) + 32
  -- (1) the derivative graph of `∂₀ f`
  have hder0 : derivGraph f (0 : Fin (m + 1)) ∈ S.Ω a bd ((m + 1) + 1) := hb D f 0 hf
  -- (2) the three blocks
  have hD1 : derivBlock f ∈ S.Ω (a + cA) qA (2 + (m + 1)) := by
    have h := Work.WilG5.coordPre_mem (S := S) (m := m + 2) (N := 2 + (m + 1))
      (ι := gZ m) (h := hder0)
    refine Work.WilG5.mem_mono h (a + cA) qA ?_ ?_
    · dsimp only [cA]; omega
    · dsimp only [qA, eA]; omega
  have hC1 : cubeBlock m ∈ S.Ω ((4 * m + 24) + cC) qC (2 + (m + 1)) := by
    have h := Work.WilG5.coordPre_mem (S := S) (m := m) (N := 2 + (m + 1))
      (ι := gY m) (h := Work.WilG5.openCube_mem (S := S) (n := m))
    refine Work.WilG5.mem_mono h ((4 * m + 24) + cC) qC ?_ ?_
    · dsimp only [cC]; omega
    · dsimp only [qC, eC]; omega
  have hB1 : absBlock m ∈ S.Ω ((2 + (m + 1)) + 4) 8 (2 + (m + 1)) := absBlock_mem S m
  -- common format
  have hDg : derivBlock f ∈ S.Ω Fg qA (2 + (m + 1)) :=
    Work.WilG5.mem_mono hD1 Fg qA (by dsimp only [Fg, cA]; omega) le_rfl
  have hCg : cubeBlock m ∈ S.Ω Fg qC (2 + (m + 1)) :=
    Work.WilG5.mem_mono hC1 Fg qC (by dsimp only [Fg, cC]; omega) le_rfl
  have hBg : absBlock m ∈ S.Ω Fg 8 (2 + (m + 1)) :=
    Work.WilG5.mem_mono hB1 Fg 8 (by dsimp only [Fg]; omega) le_rfl
  -- (3) the joint set
  have hCB : cubeBlock m ∩ absBlock m ∈ S.Ω (Fg + 1) (qC + 8) (2 + (m + 1)) := by
    have h := S.inter (F := Fg) (fun i : Fin 2 => if i = 0 then qC else 8)
      (fun i : Fin 2 => if i = 0 then cubeBlock m else absBlock m)
      (by intro i
          fin_cases i
          · simpa using hCg
          · simpa using hBg)
    rw [show (∑ i : Fin 2, (if i = 0 then qC else 8)) = qC + 8 from by
      simp [Fin.sum_univ_two]] at h
    rwa [Work.WilG1.Omega.iInter_fin_two] at h
  have hBIG : BIG f ∈ S.Ω (Fg + 2) qBIG (2 + (m + 1)) := by
    have hDg' : derivBlock f ∈ S.Ω (Fg + 1) qA (2 + (m + 1)) :=
      Work.WilG5.mem_mono hDg (Fg + 1) qA (by omega) le_rfl
    have h := S.inter (F := Fg + 1) (fun i : Fin 2 => if i = 0 then qA else qC + 8)
      (fun i : Fin 2 => if i = 0 then derivBlock f else (cubeBlock m ∩ absBlock m))
      (by intro i
          fin_cases i
          · simpa using hDg'
          · simpa using hCB)
    rw [show (∑ i : Fin 2, (if i = 0 then qA else qC + 8)) = qA + (qC + 8) from by
      simp [Fin.sum_univ_two]] at h
    rw [Work.WilG1.Omega.iInter_fin_two] at h
    refine Work.WilG5.mem_mono h (Fg + 2) qBIG ?_ ?_
    · omega
    · dsimp only [qBIG]; omega
  -- (4) project the `(y,t)`-block and quantify `M` universally
  have hL : Work.WilG5.projN (m + 1) (BIG f) ∈ S.Ω (Fg + 2 + (m + 1)) qBIG 2 :=
    Work.WilG5.projN_mem (S := S) (n := 2) (m + 1) (Fg + 2) qBIG hBIG
  have hLc : (Work.WilG5.projN (m + 1) (BIG f))ᶜ ∈ S.Ω (Fg + 2 + (m + 1) + 1) qBIG 2 :=
    S.compl hL
  have hIm : Work.WilG5.coordImage gE1 (Work.WilG5.projN (m + 1) (BIG f))ᶜ
      ∈ S.Ω (Fg + 2 + (m + 1) + 1 + 64 * (2 + 1) + 64) (qBIG + 32 * (2 + 1) + 32) 1 :=
    Work.WilG5.coordImage_mem (S := S) (m := 1) (N := 2) (ι := gE1) hLc
  have hBC : badCore f ∈ S.Ω (Fg + 2 + (m + 1) + 1 + 64 * (2 + 1) + 64 + 1) qI 1 := by
    have h := S.compl hIm
    rw [badCore_eq] at h
    refine Work.WilG5.mem_mono h (Fg + 2 + (m + 1) + 1 + 64 * (2 + 1) + 64 + 1) qI ?_ ?_
    · omega
    · dsimp only [qI]; omega
  -- (5) the elementary conditions and the final intersection
  have hBC2 : badCore f ∈ S.Ω Fg2 qI 1 :=
    Work.WilG5.mem_mono hBC Fg2 qI (by dsimp only [Fg2]; omega) le_rfl
  have hA2 : {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo (0 : ℝ) 1} ∈ S.Ω Fg2 16 1 :=
    Work.WilG5.mem_mono (interval_mem S D) Fg2 16
      (by dsimp only [Fg2]; omega) (by simp)
  have hB2 : {x : Fin 1 → ℝ | x 0 ∉ (s : Set ℝ)} ∈ S.Ω Fg2 (s.card + 4) 1 :=
    Work.WilG5.mem_mono (notMem_mem S s D) Fg2 (s.card + 4)
      (by dsimp only [Fg2]; omega) (by simp)
  have hI1 : (badCore f ∩ {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo (0 : ℝ) 1})
      ∈ S.Ω (Fg2 + 1) (qI + 16) 1 := by
    have h := S.inter (F := Fg2) (fun i : Fin 2 => if i = 0 then qI else 16)
      (fun i : Fin 2 => if i = 0 then badCore f
        else {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo (0 : ℝ) 1})
      (by intro i
          fin_cases i
          · simpa using hBC2
          · simpa using hA2)
    rw [show (∑ i : Fin 2, (if i = 0 then qI else 16)) = qI + 16 from by
      simp [Fin.sum_univ_two]] at h
    rwa [Work.WilG1.Omega.iInter_fin_two] at h
  have hI2 : ((badCore f ∩ {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo (0 : ℝ) 1})
        ∩ {x : Fin 1 → ℝ | x 0 ∉ (s : Set ℝ)})
      ∈ S.Ω (Fg2 + 2) ((qI + 16) + (s.card + 4)) 1 := by
    have hB2' : {x : Fin 1 → ℝ | x 0 ∉ (s : Set ℝ)} ∈ S.Ω (Fg2 + 1) (s.card + 4) 1 :=
      Work.WilG5.mem_mono hB2 (Fg2 + 1) (s.card + 4) (by omega) le_rfl
    have h := S.inter (F := Fg2 + 1) (fun i : Fin 2 => if i = 0 then (qI + 16) else (s.card + 4))
      (fun i : Fin 2 => if i = 0 then (badCore f ∩ {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo (0 : ℝ) 1})
        else {x : Fin 1 → ℝ | x 0 ∉ (s : Set ℝ)})
      (by intro i
          fin_cases i
          · simpa using hI1
          · simpa using hB2')
    rw [show (∑ i : Fin 2, (if i = 0 then (qI + 16) else (s.card + 4)))
        = (qI + 16) + (s.card + 4) from by simp [Fin.sum_univ_two]] at h
    rwa [Work.WilG1.Omega.iInter_fin_two] at h
  rw [badSet_eq f s]
  refine Work.WilG5.mem_mono hI2 (F + (Fg2 + 2))
    ((Work.WilG1.psubst b 1 + Polynomial.C cc).eval D) ?_ ?_
  · dsimp only [Fg2]; omega
  · dsimp only [cc, eA, eC, qI, qBIG, qA, qC, bd]
    simp only [Polynomial.eval_add, Polynomial.eval_C, Work.WilG1.eval_psubst]
    omega

end Work.WilG4b
