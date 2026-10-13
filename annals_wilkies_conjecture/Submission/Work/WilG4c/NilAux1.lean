/-
  WilG4c / `NilAux1` — coordinate, evaluation and gadget lemmas for `AlDgListSliceNil`.
-/
import Mathlib
import Submission.Work.WilG4c.SliceNilDefs
import Submission.Work.WilG4c.graphReduce.mem_famGraph_comp_iotaVp

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

theorem mem_famGraph_comp_iotaVp' (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (u : Fin (Kz p n + 2) → ℝ) :
    (u ∘ iotaVp p n) ∈ WilkiesDesign.CG.famGraph f ↔
      u (vpPos p n) = f (fun i : Fin p => u (lPos p n i))
        (fun j : Fin (n + 1) => u (ypPos p n j)) :=
  _root_.Work.WilG4c.graphReduce.mem_famGraph_comp_iotaVp p n f u

/-! ## `Fin.snoc` bookkeeping -/

theorem init_snoc' {m : ℕ} (w : Fin m → ℝ) (s : ℝ) :
    Fin.init (Fin.snoc w s : Fin (m + 1) → ℝ) = w := by
  funext i
  exact congrFun (Fin.snoc_comp_castSucc (f := w) (a := s)) i

theorem snoc_last' {m : ℕ} (w : Fin m → ℝ) (s : ℝ) :
    (Fin.snoc w s : Fin (m + 1) → ℝ) (Fin.last m) = s := by
  simp [Fin.snoc]

theorem snoc_cast' {m : ℕ} (w : Fin m → ℝ) (s : ℝ) (i : Fin m) :
    (Fin.snoc w s : Fin (m + 1) → ℝ) (Fin.castSucc i) = w i := by
  simp [Fin.snoc]

/-! ## The gadget conversions -/

theorem exists_sq_mul_sub_one (c : ℝ) : (∃ t : ℝ, t ^ 2 * c - 1 = 0) ↔ 0 < c := by
  constructor
  · rintro ⟨t, ht⟩
    nlinarith [sq_nonneg t, sq_nonneg c]
  · intro hc
    refine ⟨(Real.sqrt c)⁻¹, ?_⟩
    have hs : Real.sqrt c ^ 2 = c := Real.sq_sqrt (le_of_lt hc)
    have hne : c ≠ 0 := ne_of_gt hc
    rw [inv_pow, hs, inv_mul_cancel₀ hne]
    ring

theorem not_exists_sq_gadget (Y : ℝ → Prop) :
    (¬∃ ε t : ℝ, t ^ 2 * ε - 1 = 0 ∧ ¬ Y ε) ↔ ∀ ε, 0 < ε → Y ε := by
  constructor
  · intro h ε hε
    by_contra hY
    refine h ⟨ε, (Real.sqrt ε)⁻¹, ?_, hY⟩
    have hs : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt (le_of_lt hε)
    have hne : ε ≠ 0 := ne_of_gt hε
    rw [inv_pow, hs, inv_mul_cancel₀ hne]
    ring
  · rintro h ⟨ε, t, ht, hY⟩
    have hε : 0 < ε := by nlinarith [sq_nonneg t]
    exact hY (h ε hε)

theorem exists_sq_gadget_pos (Z : ℝ → Prop) :
    (∃ δ t : ℝ, t ^ 2 * δ - 1 = 0 ∧ Z δ) ↔ ∃ δ, 0 < δ ∧ Z δ := by
  constructor
  · rintro ⟨δ, t, ht, hZ⟩
    exact ⟨δ, by nlinarith [sq_nonneg t], hZ⟩
  · rintro ⟨δ, hδ, hZ⟩
    refine ⟨δ, (Real.sqrt δ)⁻¹, ?_, hZ⟩
    have hs : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt (le_of_lt hδ)
    have hne : δ ≠ 0 := ne_of_gt hδ
    rw [inv_pow, hs, inv_mul_cancel₀ hne]
    ring

theorem not_exists_sq_gadget_const (c : ℝ) (W : Prop) :
    (¬∃ t : ℝ, t ^ 2 * c - 1 = 0 ∧ ¬ W) ↔ (0 < c → W) := by
  constructor
  · intro h hc
    by_contra hW
    refine h ⟨(Real.sqrt c)⁻¹, ?_, hW⟩
    have hs : Real.sqrt c ^ 2 = c := Real.sq_sqrt (le_of_lt hc)
    have hne : c ≠ 0 := ne_of_gt hc
    rw [inv_pow, hs, inv_mul_cancel₀ hne]
    ring
  · rintro h ⟨t, ht, hW⟩
    have hc : 0 < c := by nlinarith [sq_nonneg t]
    exact hW (h hc)

theorem exists_eq_and_pos (A ε v : ℝ) :
    (∃ v' : ℝ, v' = A ∧ 0 < ε ^ 2 - (v' - v) ^ 2) ↔ 0 < ε ^ 2 - (A - v) ^ 2 := by
  constructor
  · rintro ⟨v', rfl, h⟩
    exact h
  · intro h
    exact ⟨A, rfl, h⟩

/-! ## Evaluations of the gadget atoms -/

theorem eval_Peps (p n : ℕ) (z : Fin (Nc p n + 1) → ℝ) (ε : ℝ) :
    MvPolynomial.eval (Fin.snoc z ε : Fin (Nc p n + 2) → ℝ) (Peps p n) = ε := by
  simp only [Peps, MvPolynomial.eval_X]
  rw [show (⟨Nc p n + 1, by omega⟩ : Fin (Nc p n + 2)) = Fin.last (Nc p n + 1)
    from Fin.ext rfl]
  exact snoc_last' z ε

theorem eval_posAtom_Peps (p n : ℕ) (z : Fin (Nc p n + 1) → ℝ) (ε t : ℝ) :
    MvPolynomial.eval (Fin.snoc (Fin.snoc z ε) t : Fin (Nc p n + 3) → ℝ) (posAtom (Peps p n))
      = t ^ 2 * ε - 1 := by
  rw [eval_posAtom, snoc_last' (Fin.snoc z ε) t, init_snoc' (Fin.snoc z ε) t]
  rw [eval_Peps]

theorem eval_posAtom_Pdel (p n : ℕ) (y : Fin (Nc p n + 4) → ℝ) (t : ℝ) :
    MvPolynomial.eval (Fin.snoc y t : Fin (Nc p n + 5) → ℝ) (posAtom (Pdel p n))
      = t ^ 2 * (y ⟨Nc p n + 3, by omega⟩) - 1 := by
  rw [eval_posAtom, snoc_last' y t, init_snoc' y t]
  simp only [Pdel, MvPolynomial.eval_X]

theorem eval_posAtom_Pball (p n : ℕ) (y : Fin (Kz p n) → ℝ) (t : ℝ) :
    MvPolynomial.eval (Fin.snoc y t : Fin (Kz p n + 1) → ℝ) (posAtom (Pball p n))
      = t ^ 2 * (MvPolynomial.eval y (Pball p n)) - 1 := by
  rw [eval_posAtom, snoc_last' y t, init_snoc' y t]

theorem eval_PD (p n : ℕ) (y : Fin (Kz p n) → ℝ) (v t : ℝ) :
    MvPolynomial.eval (Fin.snoc (Fin.snoc y v) t : Fin (Kz p n + 2) → ℝ) (PD p n)
      = (y ⟨Nc p n + 1, by simp only [Kz, Nc]; omega⟩) ^ 2 -
          (t - y ⟨Nc p n, by simp only [Kz, Nc]; omega⟩) ^ 2 := by
  rw [PD]
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_pow, MvPolynomial.eval_X]
  rw [show (⟨Nc p n + 1, by simp only [Kz, Nc]; omega⟩ : Fin (Kz p n + 2)) =
      Fin.castSucc (Fin.castSucc (⟨Nc p n + 1, by simp only [Kz, Nc]; omega⟩ : Fin (Kz p n)))
    from Fin.ext rfl, snoc_cast', snoc_cast']
  rw [show (⟨Kz p n + 1, by simp only [Kz, Nc]; omega⟩ : Fin (Kz p n + 2)) =
      Fin.last (Kz p n + 1) from Fin.ext rfl, snoc_last' (Fin.snoc y v) t]
  rw [show (⟨Nc p n, by simp only [Kz, Nc]; omega⟩ : Fin (Kz p n + 2)) =
      Fin.castSucc (Fin.castSucc (⟨Nc p n, by simp only [Kz, Nc]; omega⟩ : Fin (Kz p n)))
    from Fin.ext rfl, snoc_cast', snoc_cast']



theorem snocIt_castAdd' (p n : ℕ) (x : Fin (Nc p n + 5) → ℝ) (w : Fin (n + 1) → ℝ)
    (i : Fin (Nc p n + 5)) :
    (Work.WilG0.snocIt (Nc p n + 5) (n + 1) x w) (Fin.castAdd (n + 1) i) = x i :=
  Work.WilG0.snocIt_castAdd _ _ _ _ _

theorem snocIt_natAdd' (p n : ℕ) (x : Fin (Nc p n + 5) → ℝ) (w : Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) :
    (Work.WilG0.snocIt (Nc p n + 5) (n + 1) x w) (Fin.natAdd (Nc p n + 5) j) = w j :=
  Work.WilG0.snocIt_natAdd _ _ _ _ _

/-! ## The `iotaVp` coordinates and the graph reduction -/

theorem iotaVp_castAdd (p n : ℕ) (i : Fin p) :
    iotaVp p n (Fin.castAdd ((n + 1) + 1) i) = lPos p n i := by
  simp only [iotaVp, Fin.append_left]

theorem iotaVp_y (p n : ℕ) (j : Fin (n + 1)) :
    iotaVp p n (Fin.natAdd p (Fin.castSucc j)) = ypPos p n j := by
  simp only [iotaVp, Fin.append_right]
  rw [show (Fin.castSucc j : Fin ((n + 1) + 1)) = Fin.castAdd 1 j from Fin.ext rfl,
    Fin.append_left]

theorem iotaVp_last (p n : ℕ) :
    iotaVp p n (Fin.natAdd p (Fin.last (n + 1))) = vpPos p n := by
  simp only [iotaVp, Fin.append_right]
  rw [show (Fin.last (n + 1) : Fin ((n + 1) + 1)) = Fin.natAdd (n + 1) (Fin.last 0)
    from Fin.ext rfl]
  simp only [Fin.append_right]

theorem comp_iotaVp_last (p n : ℕ) (u : Fin (Kz p n + 2) → ℝ) :
    (u ∘ iotaVp p n) (Fin.last (Nc p n)) = u (vpPos p n) := by
  simp only [Function.comp_apply]
  rw [show (Fin.last (Nc p n) : Fin (Ng p n)) = Fin.natAdd p (Fin.last (n + 1))
    from Fin.ext rfl, iotaVp_last]

theorem init_comp_iotaVp (p n : ℕ) (u : Fin (Kz p n + 2) → ℝ) :
    Fin.init (u ∘ iotaVp p n) =
      Fin.append (fun i : Fin p => u (lPos p n i)) (fun j : Fin (n + 1) => u (ypPos p n j)) := by
  funext i
  cases i using Fin.addCases with
  | left i' =>
      rw [Fin.append_left]
      simp only [Function.comp_apply, Fin.init]
      rw [show (Fin.castSucc (Fin.castAdd (n + 1) i') : Fin (Ng p n))
          = Fin.castAdd ((n + 1) + 1) i' from Fin.ext rfl, iotaVp_castAdd]
  | right j =>
      rw [Fin.append_right]
      simp only [Function.comp_apply, Fin.init]
      rw [show (Fin.castSucc (Fin.natAdd p j) : Fin (Ng p n)) = Fin.natAdd p (Fin.castSucc j)
          from Fin.ext rfl, iotaVp_y]



/-- The `Pball` evaluation on the glued vector. -/
theorem eval_Pball_snocIt (p n : ℕ) (x : Fin (Nc p n + 5) → ℝ) (w : Fin (n + 1) → ℝ) :
    MvPolynomial.eval (Work.WilG0.snocIt (Nc p n + 5) (n + 1) x w) (Pball p n)
      = (x ⟨Nc p n + 3, by omega⟩) ^ 2 -
          ∑ j : Fin (n + 1), (w j - x ⟨p + (j : ℕ), by simp only [Nc]; omega⟩) ^ 2 := by
  have h1 : MvPolynomial.eval (Work.WilG0.snocIt (Nc p n + 5) (n + 1) x w)
      (MvPolynomial.X ⟨Nc p n + 3, by simp only [Kz, Nc]; omega⟩ : MvPolynomial (Fin (Kz p n)) ℝ)
      = x ⟨Nc p n + 3, by omega⟩ := by
    simp only [MvPolynomial.eval_X]
    rw [show (⟨Nc p n + 3, by simp only [Kz, Nc]; omega⟩ : Fin (Kz p n)) =
        Fin.castAdd (n + 1) ⟨Nc p n + 3, by omega⟩ from Fin.ext rfl, snocIt_castAdd']
  have h2 : ∀ j : Fin (n + 1), MvPolynomial.eval (Work.WilG0.snocIt (Nc p n + 5) (n + 1) x w)
      ((MvPolynomial.X ⟨Nc p n + 5 + (j : ℕ), by simp only [Kz, Nc]; omega⟩ -
        MvPolynomial.X ⟨p + (j : ℕ), by simp only [Kz, Nc]; omega⟩) ^ 2
          : MvPolynomial (Fin (Kz p n)) ℝ)
      = (w j - x ⟨p + (j : ℕ), by simp only [Nc]; omega⟩) ^ 2 := by
    intro j
    simp only [MvPolynomial.eval_sub, MvPolynomial.eval_pow, MvPolynomial.eval_X]
    rw [show (⟨Nc p n + 5 + (j : ℕ), by simp only [Kz, Nc]; omega⟩ : Fin (Kz p n)) =
        Fin.natAdd (Nc p n + 5) j from Fin.ext rfl, snocIt_natAdd']
    rw [show (⟨p + (j : ℕ), by simp only [Kz, Nc]; omega⟩ : Fin (Kz p n)) =
        Fin.castAdd (n + 1) ⟨p + (j : ℕ), by simp only [Nc]; omega⟩ from Fin.ext rfl,
        snocIt_castAdd']
  rw [Pball, MvPolynomial.eval_sub, MvPolynomial.eval_pow, h1, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => h2 j

/-- The `l`-coordinate of the `v'`-point of the shape. -/
theorem snocIt_coord_lPos (p n : ℕ) (x : Fin (Nc p n + 5) → ℝ) (w : Fin (n + 1) → ℝ)
    (ts v' : ℝ) (i : Fin p) :
    ((Fin.snoc (Fin.snoc (Work.WilG0.snocIt (Nc p n + 5) (n + 1) x w) ts) v')
      : Fin (Kz p n + 2) → ℝ) (lPos p n i) = x ⟨(i : ℕ), by simp only [Nc]; omega⟩ := by
  rw [show lPos p n i = Fin.castSucc (Fin.castSucc
      (⟨(i : ℕ), by simp only [Kz, Nc]; omega⟩ : Fin (Kz p n))) from Fin.ext rfl,
    snoc_cast', snoc_cast']
  rw [show (⟨(i : ℕ), by simp only [Kz, Nc]; omega⟩ : Fin (Kz p n)) =
      Fin.castAdd (n + 1) ⟨(i : ℕ), by simp only [Nc]; omega⟩ from Fin.ext rfl, snocIt_castAdd']

/-- The `y'`-coordinate of the `v'`-point of the shape. -/
theorem snocIt_coord_ypPos (p n : ℕ) (x : Fin (Nc p n + 5) → ℝ) (w : Fin (n + 1) → ℝ)
    (ts v' : ℝ) (j : Fin (n + 1)) :
    ((Fin.snoc (Fin.snoc (Work.WilG0.snocIt (Nc p n + 5) (n + 1) x w) ts) v')
      : Fin (Kz p n + 2) → ℝ) (ypPos p n j) = w j := by
  rw [show ypPos p n j = Fin.castSucc (Fin.castSucc
      (Fin.natAdd (Nc p n + 5) j : Fin (Kz p n))) from Fin.ext rfl,
    snoc_cast', snoc_cast', snocIt_natAdd']

/-- The `v'`-coordinate of the `v'`-point of the shape. -/
theorem snocIt_coord_vpPos (p n : ℕ) (x : Fin (Nc p n + 5) → ℝ) (w : Fin (n + 1) → ℝ)
    (ts v' : ℝ) :
    ((Fin.snoc (Fin.snoc (Work.WilG0.snocIt (Nc p n + 5) (n + 1) x w) ts) v')
      : Fin (Kz p n + 2) → ℝ) (vpPos p n) = v' := by
  rw [show vpPos p n = Fin.last (Kz p n + 1) from Fin.ext rfl]
  exact snoc_last' _ v'

/-- The graph reduction for the `v'`-point of the shape. -/
theorem famGraph_snocIt_iotaVp (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (x : Fin (Nc p n + 5) → ℝ) (w : Fin (n + 1) → ℝ) (ts v' : ℝ) :
    (Fin.snoc (Fin.snoc (Work.WilG0.snocIt (Nc p n + 5) (n + 1) x w) ts) v' ∘ iotaVp p n)
        ∈ famGraph f ↔
      v' = f (fun i : Fin p => x ⟨(i : ℕ), by simp only [Nc]; omega⟩) w := by
  have hvp := snocIt_coord_vpPos p n x w ts v'
  have hl : (fun i : Fin p => ((Fin.snoc (Fin.snoc (Work.WilG0.snocIt (Nc p n + 5) (n + 1) x w) ts) v')
        : Fin (Kz p n + 2) → ℝ) (lPos p n i)) = fun i : Fin p => x ⟨(i : ℕ), by simp only [Nc]; omega⟩ :=
    funext fun i => snocIt_coord_lPos p n x w ts v' i
  have hy : (fun j : Fin (n + 1) => ((Fin.snoc (Fin.snoc (Work.WilG0.snocIt (Nc p n + 5) (n + 1) x w) ts) v')
        : Fin (Kz p n + 2) → ℝ) (ypPos p n j)) = w := funext fun j => snocIt_coord_ypPos p n x w ts v' j
  have hmem := mem_famGraph_comp_iotaVp' p n f
    (Fin.snoc (Fin.snoc (Work.WilG0.snocIt (Nc p n + 5) (n + 1) x w) ts) v')
  rw [hvp, hl, hy] at hmem
  exact hmem

/-- The `Pdel` atom at the shape's chain. -/
theorem eval_chain_Pdel (p n : ℕ) (z : Fin (Nc p n + 1) → ℝ) (ε τ δ tδ : ℝ) :
    MvPolynomial.eval (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc z ε) τ) δ) tδ
        : Fin (Nc p n + 5) → ℝ) (posAtom (Pdel p n)) = tδ ^ 2 * δ - 1 := by
  rw [eval_posAtom, snoc_last' _ tδ, init_snoc' _ tδ]
  have h : MvPolynomial.eval (Fin.snoc (Fin.snoc (Fin.snoc z ε) τ) δ : Fin (Nc p n + 4) → ℝ)
      (Pdel p n) = δ := by
    simp only [Pdel, MvPolynomial.eval_X]
    rw [show (⟨Nc p n + 3, by omega⟩ : Fin (Nc p n + 4)) = Fin.last (Nc p n + 3)
      from Fin.ext rfl]
    exact snoc_last' _ δ
  rw [h]

/-- The `Pball` atom at the shape's chain. -/
theorem eval_chain_Pball (p n : ℕ) (z : Fin (Nc p n + 1) → ℝ) (ε τ δ tδ : ℝ)
    (w : Fin (n + 1) → ℝ) (ts : ℝ) :
    MvPolynomial.eval (Fin.snoc (Work.WilG0.snocIt (Nc p n + 5) (n + 1)
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc z ε) τ) δ) tδ) w) ts
        : Fin (Kz p n + 1) → ℝ) (posAtom (Pball p n))
      = ts ^ 2 * (δ ^ 2 - ∑ j : Fin (n + 1),
          (w j - z ⟨p + (j : ℕ), by simp only [Nc]; omega⟩) ^ 2) - 1 := by
  rw [eval_posAtom, snoc_last' _ ts, init_snoc' _ ts, eval_Pball_snocIt]
  have h3 : ((Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc z ε) τ) δ) tδ
        : Fin (Nc p n + 5) → ℝ) ⟨Nc p n + 3, by omega⟩ : ℝ) = δ := by
    rw [show (⟨Nc p n + 3, by omega⟩ : Fin (Nc p n + 5))
        = Fin.castSucc (Fin.last (Nc p n + 3)) from Fin.ext rfl, snoc_cast', snoc_last']
  have h4 : ∀ j : Fin (n + 1),
      ((Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc z ε) τ) δ) tδ
        : Fin (Nc p n + 5) → ℝ) ⟨p + (j : ℕ), by simp only [Nc]; omega⟩ : ℝ)
      = z ⟨p + (j : ℕ), by simp only [Nc]; omega⟩ := by
    intro j
    rw [show (⟨p + (j : ℕ), by simp only [Nc]; omega⟩ : Fin (Nc p n + 5))
        = Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.castSucc
          (⟨p + (j : ℕ), by simp only [Nc]; omega⟩ : Fin (Nc p n + 1))))) from Fin.ext rfl,
      snoc_cast', snoc_cast', snoc_cast', snoc_cast']
  rw [h3]
  have hsum : (∑ j : Fin (n + 1),
        (w j - ((Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc z ε) τ) δ) tδ
          : Fin (Nc p n + 5) → ℝ) ⟨p + (j : ℕ), by simp only [Nc]; omega⟩)) ^ 2)
      = ∑ j : Fin (n + 1), (w j - z ⟨p + (j : ℕ), by simp only [Nc]; omega⟩) ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [h4 j]
  rw [hsum]

/-- The `PD` atom at the shape's chain. -/
theorem eval_chain_PD (p n : ℕ) (z : Fin (Nc p n + 1) → ℝ) (ε τ δ tδ : ℝ)
    (w : Fin (n + 1) → ℝ) (ts v' : ℝ) :
    MvPolynomial.eval (Fin.snoc (Fin.snoc (Work.WilG0.snocIt (Nc p n + 5) (n + 1)
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc z ε) τ) δ) tδ) w) ts) v'
        : Fin (Kz p n + 2) → ℝ) (PD p n)
      = ε ^ 2 - (v' - z ⟨Nc p n, by simp only [Nc]; omega⟩) ^ 2 := by
  rw [eval_PD]
  have h1 : (Work.WilG0.snocIt (Nc p n + 5) (n + 1)
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc z ε) τ) δ) tδ) w
        : Fin (Kz p n) → ℝ) ⟨Nc p n + 1, by simp only [Kz, Nc]; omega⟩ = ε := by
    rw [show (⟨Nc p n + 1, by simp only [Kz, Nc]; omega⟩ : Fin (Kz p n))
        = Fin.castAdd (n + 1) (⟨Nc p n + 1, by simp only [Nc]; omega⟩ : Fin (Nc p n + 5))
        from Fin.ext rfl, snocIt_castAdd']
    rw [show (⟨Nc p n + 1, by simp only [Nc]; omega⟩ : Fin (Nc p n + 5))
        = Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.last (Nc p n + 1))))
        from Fin.ext rfl, snoc_cast', snoc_cast', snoc_cast', snoc_last']
  have h2 : (Work.WilG0.snocIt (Nc p n + 5) (n + 1)
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc z ε) τ) δ) tδ) w
        : Fin (Kz p n) → ℝ) ⟨Nc p n, by simp only [Kz, Nc]; omega⟩
      = z ⟨Nc p n, by simp only [Nc]; omega⟩ := by
    rw [show (⟨Nc p n, by simp only [Kz, Nc]; omega⟩ : Fin (Kz p n))
        = Fin.castAdd (n + 1) (⟨Nc p n, by simp only [Nc]; omega⟩ : Fin (Nc p n + 5))
        from Fin.ext rfl, snocIt_castAdd']
    rw [show (⟨Nc p n, by simp only [Nc]; omega⟩ : Fin (Nc p n + 5))
        = Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.castSucc
          (⟨Nc p n, by simp only [Nc]; omega⟩ : Fin (Nc p n + 1))))) from Fin.ext rfl,
      snoc_cast', snoc_cast', snoc_cast', snoc_cast']
  rw [h1, h2]

theorem sub_sq_pos_iff (ε A : ℝ) : 0 < ε ^ 2 - A ^ 2 ↔ A ^ 2 < ε ^ 2 := by
  constructor <;> intro h <;> linarith

/-! ## Coordinates of the shape's chain, in the free coordinates

These are the forms in which the `eval_chain_*` lemmas present the coordinates of the glued
vector, so that the final unwinding of `ContSet` can be done by rewriting with them. -/

/-- The `ε`-coordinate of the shape's chain. -/
theorem chain_eps (p n : ℕ) (z : Fin (Nc p n + 1) → ℝ) (ε τ δ tδ : ℝ) :
    ((Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc z ε) τ) δ) tδ : Fin (Nc p n + 5) → ℝ)
      ⟨Nc p n + 1, by omega⟩ : ℝ) = ε := by
  rw [show (⟨Nc p n + 1, by omega⟩ : Fin (Nc p n + 5))
      = Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.last (Nc p n + 1))))
      from Fin.ext rfl, snoc_cast', snoc_cast', snoc_cast', snoc_last']

/-- The `δ`-coordinate of the shape's chain. -/
theorem chain_del (p n : ℕ) (z : Fin (Nc p n + 1) → ℝ) (ε τ δ tδ : ℝ) :
    ((Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc z ε) τ) δ) tδ : Fin (Nc p n + 5) → ℝ)
      ⟨Nc p n + 3, by omega⟩ : ℝ) = δ := by
  rw [show (⟨Nc p n + 3, by omega⟩ : Fin (Nc p n + 5))
      = Fin.castSucc (Fin.last (Nc p n + 3)) from Fin.ext rfl, snoc_cast', snoc_last']

/-- The `z`-coordinates of the shape's chain. -/
theorem chain_z (p n : ℕ) (z : Fin (Nc p n + 1) → ℝ) (ε τ δ tδ : ℝ)
    (i : Fin (Nc p n + 1)) :
    ((Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc z ε) τ) δ) tδ : Fin (Nc p n + 5) → ℝ)
      ⟨(i : ℕ), by omega⟩ : ℝ) = z i := by
  rw [show (⟨(i : ℕ), by omega⟩ : Fin (Nc p n + 5))
      = Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.castSucc i))) from Fin.ext rfl,
    snoc_cast', snoc_cast', snoc_cast', snoc_cast']

/-- The graph reduction at the shape's chain, in the coordinates of the free point. -/
theorem famGraph_chain_iotaVp (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (z : Fin (Nc p n + 1) → ℝ) (ε τ δ tδ : ℝ) (w : Fin (n + 1) → ℝ) (ts v' : ℝ) :
    (Fin.snoc (Fin.snoc (Work.WilG0.snocIt (Nc p n + 5) (n + 1)
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc z ε) τ) δ) tδ) w) ts) v' ∘ iotaVp p n)
        ∈ famGraph f ↔
      v' = f (fun i : Fin p => z ⟨(i : ℕ), by simp only [Nc]; omega⟩) w := by
  rw [famGraph_snocIt_iotaVp]
  rw [show (fun i : Fin p => (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc z ε) τ) δ) tδ
        : Fin (Nc p n + 5) → ℝ) ⟨(i : ℕ), by simp only [Nc]; omega⟩)
      = fun i : Fin p => z ⟨(i : ℕ), by simp only [Nc]; omega⟩ from
    funext fun i => chain_z p n z ε τ δ tδ ⟨(i : ℕ), by simp only [Nc]; omega⟩]

/-! ## The free coordinates read off `Fin.init z` -/

theorem parPt_init_eq (p n : ℕ) (z : Fin (Nc p n + 1) → ℝ) :
    parPt (Fin.init z) = fun i : Fin p => z ⟨(i : ℕ), by simp only [Nc]; omega⟩ := by
  funext i
  exact congrArg z (Fin.ext rfl)

theorem cubePt_init_eq (p n : ℕ) (z : Fin (Nc p n + 1) → ℝ) :
    cubePt (Fin.init z) = fun j : Fin (n + 1) => z ⟨p + (j : ℕ), by simp only [Nc]; omega⟩ := by
  funext j
  exact congrArg z (Fin.ext rfl)

end Work.WilkG4c
