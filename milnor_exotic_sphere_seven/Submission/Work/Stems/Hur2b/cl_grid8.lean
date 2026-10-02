import Mathlib
import Submission.Work.Stems.Hur2b.NetLayout

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `cl_grid8`: the `8 × 8` grid subdivision of a based `2`-cube

Let `p : Ω²(X,x₀)` be a based `2`-cube which is `x₀` on the boundary of *every* cell of the uniform
`8 × 8` grid of the square (that is, each of the `64` affine cell readings of `p` is a based cube).
Then the class of `p` in `π₂(X,x₀)` is the product of the classes of the `64` cell readings.

The proof is the classical subdivision argument.

* `bArr i r cs` is the *balanced* nested concatenation (in the coordinate `i`) of `2^r` based cubes;
  against the naive nested concatenation its advantage is that the associated fold map is the
  identity, which makes `bArr i r (fun k => q ∘ ψ_k) = q` provable by induction (`bArr_vCube`,
  `bArr_hCube`), the two halves being dealt with by `transAt_vCube` / `transAt_hCube`.
* `bArr_class` computes the class of `bArr i r cs` as the product of the classes.
* The `8 × 8` grid statement then follows by applying the vertical subdivision with `r = 3` and the
  horizontal one to each of the eight column readings; the two are intertwined by the identity
  `cellRead i k = colAff 8 i ∘ rowAff 8 k` (`colAff_rowAff`).
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical Work.Stems.Hur2

namespace Grid8

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X}

theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp

@[simp] theorem fin2_zero_coe : (((0:Fin 2)) : ℝ) = 0 := by
  rw [show ((0:Fin 2):ℕ) = 0 from rfl, Nat.cast_zero]

@[simp] theorem fin2_one_coe : (((1:Fin 2)) : ℝ) = 1 := by
  rw [show ((1:Fin 2):ℕ) = 1 from rfl, Nat.cast_one]

@[simp] theorem uI_zero_coe : ((0 : unitInterval) : ℝ) = 0 := rfl

@[simp] theorem uI_one_coe : ((1 : unitInterval) : ℝ) = 1 := rfl

theorem clamp_coe_of_mem {r : ℝ} (h : r ∈ Set.Icc (0:ℝ) 1) :
    ((clamp r : unitInterval) : ℝ) = r := by rw [clamp_of_mem h]

/-- The midpoint of the interval. -/
def halfPt : unitInterval := ⟨1/2, by norm_num⟩

@[simp] theorem halfPt_coe : ((halfPt : unitInterval) : ℝ) = 1/2 := rfl

theorem h2pow (r : ℕ) : ((2^(r+1) : ℕ) : ℝ) = ((2^r : ℕ) : ℝ) * 2 := by
  push_cast; rw [pow_succ]

/-! ## The balanced nested arrangement -/

theorem powTwo_add (r : ℕ) : 2^r + 2^r = 2^(r+1) := by rw [pow_succ]; ring

/-- The index of the `j`-th cube of the first half of the `2^(r+1)`-grid. -/
def halfA (r : ℕ) : Fin (2^r) → Fin (2^(r+1)) :=
  fun j => Fin.cast (powTwo_add r) (Fin.castAdd (2^r) j)

/-- The index of the `j`-th cube of the second half of the `2^(r+1)`-grid. -/
def halfB (r : ℕ) : Fin (2^r) → Fin (2^(r+1)) :=
  fun j => Fin.cast (powTwo_add r) (Fin.natAdd (2^r) j)

theorem halfA_val (r : ℕ) (j : Fin (2^r)) : (halfA r j : ℕ) = j := by
  simp [halfA, Fin.val_cast, Fin.val_castAdd]

theorem halfB_val (r : ℕ) (j : Fin (2^r)) : (halfB r j : ℕ) = 2^r + j := by
  simp [halfB, Fin.val_cast, Nat.add_comm]

/-- Splitting a product over the `2^(r+1)`-grid into the two halves. -/
theorem prod_split {M : Type*} [CommMonoid M] (r : ℕ) (f : Fin (2^(r+1)) → M) :
    ∏ k : Fin (2^(r+1)), f k
      = (∏ j : Fin (2^r), f (halfA r j)) * (∏ j : Fin (2^r), f (halfB r j)) := by
  have h1 : ∏ i : Fin (2^r + 2^r), f (Fin.cast (powTwo_add r) i)
      = ∏ k : Fin (2^(r+1)), f k :=
    Fintype.prod_bijective (Fin.cast (powTwo_add r))
      ⟨fun a b hab => by
        have h := congrArg Fin.val hab
        simp only [Fin.val_cast] at h
        exact Fin.ext h,
       fun b => ⟨Fin.cast (powTwo_add r).symm b, by ext; simp⟩⟩ _ _ (fun i => rfl)
  rw [← h1, Fin.prod_univ_add]
  rfl

/-- The balanced nested concatenation (in the coordinate `i`) of `2^r` based cubes: the `j`-th cube
of level `r` is placed in the `j`-th of the `2^r` equal strips. -/
noncomputable def bArr (i : Fin 2) : (r : ℕ) → (Fin (2^r) → GenLoop (Fin 2) X x₀) →
    GenLoop (Fin 2) X x₀
  | 0, cs => cs 0
  | r+1, cs => GenLoop.transAt i (bArr i r (cs ∘ halfA r)) (bArr i r (cs ∘ halfB r))

theorem bArr_zero (i : Fin 2) (cs : Fin (2^0) → GenLoop (Fin 2) X x₀) :
    bArr i 0 cs = cs 0 := rfl

theorem bArr_succ (i : Fin 2) (r : ℕ) (cs : Fin (2^(r+1)) → GenLoop (Fin 2) X x₀) :
    bArr i (r+1) cs
      = GenLoop.transAt i (bArr i r (cs ∘ halfA r)) (bArr i r (cs ∘ halfB r)) := rfl

/-- **The class of the balanced nested arrangement is the product of the classes.** -/
theorem bArr_class (r : ℕ) : ∀ (i : Fin 2) (cs : Fin (2^r) → GenLoop (Fin 2) X x₀),
    cl x₀ (bArr i r cs) = ∏ k : Fin (2^r), cl x₀ (cs k) := by
  induction r with
  | zero =>
      intro i cs
      rw [bArr_zero]
      refine (Finset.prod_eq_single (s := Finset.univ) (f := fun k : Fin (2^0) => cl x₀ (cs k))
        (0 : Fin (2^0)) ?_ ?_).symm
      · intro b _ hb
        exact absurd (Fin.ext (by have h1 : (2:ℕ)^0 = 1 := pow_zero 2
                                  have := b.isLt; omega)) hb
      · intro h; exact absurd (Finset.mem_univ _) h
  | succ r ih =>
      intro i cs
      rw [bArr_succ]
      rcases fin_two_cases i with h | h
      · rw [h, cl_transAt_zero, ih 0 (cs ∘ halfB r), ih 0 (cs ∘ halfA r)]
        simp only [Function.comp_apply]
        rw [prod_split r (fun k => cl x₀ (cs k))]
        exact mul_comm _ _
      · rw [h, cl_transAt_one, ih 1 (cs ∘ halfB r), ih 1 (cs ∘ halfA r)]
        simp only [Function.comp_apply]
        rw [prod_split r (fun k => cl x₀ (cs k))]
        exact mul_comm _ _

/-! ## The affine strip readings -/

/-- The affine reading of the `k`-th of `m` equal vertical strips of the square. -/
noncomputable def colAff (m : ℕ) (k : Fin m) : C(IC 2, IC 2) where
  toFun y := pair2 ⟨((k:ℝ) + (y 0 : ℝ))/m, by
      have hm : 0 < m := by have := k.isLt; omega
      refine ⟨div_nonneg ?_ (by positivity), ?_⟩
      · have := (y 0).2.1; linarith
      · rw [div_le_one (by exact_mod_cast hm)]
        have h1 : ((k:ℕ):ℝ) + 1 ≤ (m:ℝ) := by
          have : (k:ℕ) + 1 ≤ m := by have := k.isLt; omega
          exact_mod_cast this
        have := (y 0).2.2
        linarith⟩ (y 1)
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · refine Continuous.subtype_mk ?_ _
      have h : Continuous fun y : IC 2 => ((y 0 : unitInterval) : ℝ) :=
        continuous_subtype_val.comp (continuous_apply 0)
      fun_prop
    · exact continuous_apply 1

/-- The affine reading of the `k`-th of `m` equal horizontal strips of the square. -/
noncomputable def rowAff (m : ℕ) (k : Fin m) : C(IC 2, IC 2) where
  toFun y := pair2 (y 0) ⟨((k:ℝ) + (y 1 : ℝ))/m, by
      have hm : 0 < m := by have := k.isLt; omega
      refine ⟨div_nonneg ?_ (by positivity), ?_⟩
      · have := (y 1).2.1; linarith
      · rw [div_le_one (by exact_mod_cast hm)]
        have h1 : ((k:ℕ):ℝ) + 1 ≤ (m:ℝ) := by
          have : (k:ℕ) + 1 ≤ m := by have := k.isLt; omega
          exact_mod_cast this
        have := (y 1).2.2
        linarith⟩
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · refine Continuous.subtype_mk ?_ _
      have h : Continuous fun y : IC 2 => ((y 1 : unitInterval) : ℝ) :=
        continuous_subtype_val.comp (continuous_apply 1)
      fun_prop

@[simp] theorem colAff_apply (m : ℕ) (k : Fin m) (y : IC 2) :
    ((colAff m k y) 0 : ℝ) = ((k:ℝ) + (y 0 : ℝ))/m := rfl

@[simp] theorem colAff_apply_one (m : ℕ) (k : Fin m) (y : IC 2) : (colAff m k y) 1 = y 1 := rfl

@[simp] theorem rowAff_apply (m : ℕ) (k : Fin m) (y : IC 2) : (rowAff m k y) 0 = y 0 := rfl

@[simp] theorem rowAff_apply_one (m : ℕ) (k : Fin m) (y : IC 2) :
    ((rowAff m k y) 1 : ℝ) = ((k:ℝ) + (y 1 : ℝ))/m := rfl

/-- The key arithmetic facts behind `colAff_comp_zero` / `colAff_comp_one`. -/
theorem key_zero (r : ℕ) (A B : ℝ) :
    (((0:Fin 2) : ℝ) + (A + B)/((2^r : ℕ) : ℝ))/((2:ℕ) : ℝ)
      = (A + B)/((2^(r+1) : ℕ) : ℝ) := by
  rw [fin2_zero_coe, zero_add, h2pow r]
  field_simp
  ring_nf

theorem key_one (r : ℕ) (A B : ℝ) :
    (((1:Fin 2) : ℝ) + (A + B)/((2^r : ℕ) : ℝ))/((2:ℕ) : ℝ)
      = (((2^r : ℕ) : ℝ) + (A + B))/((2^(r+1) : ℕ) : ℝ) := by
  rw [fin2_one_coe, h2pow r]
  push_cast
  field_simp <;> ring

theorem colAff_one (y : IC 2) : colAff 1 (0 : Fin 1) y = y := by
  funext i
  rcases fin_two_cases i with h | h
  · rw [h]; apply Subtype.ext; simp
  · rw [h, colAff_apply_one]

theorem rowAff_one (y : IC 2) : rowAff 1 (0 : Fin 1) y = y := by
  funext i
  rcases fin_two_cases i with h | h
  · rw [h, rowAff_apply]
  · rw [h]; apply Subtype.ext; simp

theorem colAff_zero_eq_zero (y : IC 2) (hy : y 0 = 0) :
    colAff 2 (0 : Fin 2) y = pair2 0 (y 1) := by
  funext i
  rcases fin_two_cases i with h | h
  · rw [h]; apply Subtype.ext
    rw [colAff_apply, hy]; norm_num
  · rw [h, colAff_apply_one, pair2_one]

theorem colAff_zero_eq_half (y : IC 2) (hy : y 0 = 1) :
    colAff 2 (0 : Fin 2) y = pair2 halfPt (y 1) := by
  funext i
  rcases fin_two_cases i with h | h
  · rw [h]; apply Subtype.ext
    rw [colAff_apply, hy]; norm_num
  · rw [h, colAff_apply_one, pair2_one]

theorem colAff_one_eq_half (y : IC 2) (hy : y 0 = 0) :
    colAff 2 (1 : Fin 2) y = pair2 halfPt (y 1) := by
  funext i
  rcases fin_two_cases i with h | h
  · rw [h]; apply Subtype.ext
    rw [colAff_apply, hy]; norm_num
  · rw [h, colAff_apply_one, pair2_one]

theorem colAff_one_eq_one (y : IC 2) (hy : y 0 = 1) :
    colAff 2 (1 : Fin 2) y = pair2 1 (y 1) := by
  funext i
  rcases fin_two_cases i with h | h
  · rw [h]; apply Subtype.ext
    rw [colAff_apply, hy]; norm_num
  · rw [h, colAff_apply_one, pair2_one]

/-- The composition of two strip readings in the first coordinate is the strip reading of the
refined grid. -/
theorem colAff_comp_zero (r : ℕ) (j : Fin (2^r)) (y : IC 2) :
    colAff 2 (0 : Fin 2) (colAff (2^r) j y) = colAff (2^(r+1)) (halfA r j) y := by
  funext i
  rcases fin_two_cases i with h | h
  · rw [h]; apply Subtype.ext
    rw [colAff_apply, colAff_apply, colAff_apply, halfA_val]
    rw [fin2_zero_coe, zero_add, h2pow r]
    field_simp
    ring_nf
  · rw [h]; simp only [colAff_apply_one]

theorem colAff_comp_one (r : ℕ) (j : Fin (2^r)) (y : IC 2) :
    colAff 2 (1 : Fin 2) (colAff (2^r) j y) = colAff (2^(r+1)) (halfB r j) y := by
  funext i
  rcases fin_two_cases i with h | h
  · rw [h]; apply Subtype.ext
    rw [colAff_apply, colAff_apply, colAff_apply, halfB_val]
    rw [fin2_one_coe, h2pow r]
    push_cast
    field_simp <;> ring
  · rw [h]; simp only [colAff_apply_one]

theorem rowAff_comp_zero (r : ℕ) (j : Fin (2^r)) (y : IC 2) :
    rowAff 2 (0 : Fin 2) (rowAff (2^r) j y) = rowAff (2^(r+1)) (halfA r j) y := by
  funext i
  rcases fin_two_cases i with h | h
  · rw [h]; simp only [rowAff_apply]
  · rw [h]; apply Subtype.ext
    rw [rowAff_apply_one, rowAff_apply_one, rowAff_apply_one, halfA_val]
    rw [fin2_zero_coe, zero_add, h2pow r]
    field_simp
    ring_nf

theorem rowAff_comp_one (r : ℕ) (j : Fin (2^r)) (y : IC 2) :
    rowAff 2 (1 : Fin 2) (rowAff (2^r) j y) = rowAff (2^(r+1)) (halfB r j) y := by
  funext i
  rcases fin_two_cases i with h | h
  · rw [h]; simp only [rowAff_apply]
  · rw [h]; apply Subtype.ext
    rw [rowAff_apply_one, rowAff_apply_one, rowAff_apply_one, halfB_val]
    rw [fin2_one_coe, h2pow r]
    push_cast
    field_simp <;> ring

/-! ## Based strip readings -/

/-- The `k`-th vertical strip reading of `q`, as a based cube. -/
noncomputable def vCube (q : GenLoop (Fin 2) X x₀) (m : ℕ) (k : Fin m)
    (h : ∀ y ∈ Cube.boundary (Fin 2), q.1 (colAff m k y) = x₀) : GenLoop (Fin 2) X x₀ :=
  compGenLoop h

@[simp] theorem vCube_apply (q : GenLoop (Fin 2) X x₀) (m : ℕ) (k : Fin m)
    (h : ∀ y ∈ Cube.boundary (Fin 2), q.1 (colAff m k y) = x₀) (y : IC 2) :
    (vCube q m k h).1 y = q.1 (colAff m k y) := rfl

@[simp] theorem vCube_apply_fun (q : GenLoop (Fin 2) X x₀) (m : ℕ) (k : Fin m)
    (h : ∀ y ∈ Cube.boundary (Fin 2), q.1 (colAff m k y) = x₀) (y : IC 2) :
    (vCube q m k h) y = q.1 (colAff m k y) := compGenLoop_apply h y

/-- The `k`-th horizontal strip reading of `q`, as a based cube. -/
noncomputable def hCube (q : GenLoop (Fin 2) X x₀) (m : ℕ) (k : Fin m)
    (h : ∀ y ∈ Cube.boundary (Fin 2), q.1 (rowAff m k y) = x₀) : GenLoop (Fin 2) X x₀ :=
  compGenLoop h

@[simp] theorem hCube_apply (q : GenLoop (Fin 2) X x₀) (m : ℕ) (k : Fin m)
    (h : ∀ y ∈ Cube.boundary (Fin 2), q.1 (rowAff m k y) = x₀) (y : IC 2) :
    (hCube q m k h).1 y = q.1 (rowAff m k y) := rfl

@[simp] theorem hCube_apply_fun (q : GenLoop (Fin 2) X x₀) (m : ℕ) (k : Fin m)
    (h : ∀ y ∈ Cube.boundary (Fin 2), q.1 (rowAff m k y) = x₀) (y : IC 2) :
    (hCube q m k h) y = q.1 (rowAff m k y) := compGenLoop_apply h y

theorem sigmaA_zero_coe (t : IC 2) :
    ((Work.Stems.sigmaA (0 : Fin 2) t) 0 : unitInterval) = clamp (2 * (t 0 : ℝ)) := rfl
theorem sigmaB_zero_coe (t : IC 2) :
    ((Work.Stems.sigmaB (0 : Fin 2) t) 0 : unitInterval) = clamp (2 * (t 0 : ℝ) - 1) := rfl
theorem sigmaA_one_coe (t : IC 2) :
    ((Work.Stems.sigmaA (1 : Fin 2) t) 1 : unitInterval) = clamp (2 * (t 1 : ℝ)) := rfl
theorem sigmaB_one_coe (t : IC 2) :
    ((Work.Stems.sigmaB (1 : Fin 2) t) 1 : unitInterval) = clamp (2 * (t 1 : ℝ) - 1) := rfl
theorem sigmaA_one_other (t : IC 2) : (Work.Stems.sigmaA (0 : Fin 2) t) 1 = t 1 := rfl
theorem sigmaB_one_other (t : IC 2) : (Work.Stems.sigmaB (0 : Fin 2) t) 1 = t 1 := rfl
theorem sigmaA_zero_other (t : IC 2) : (Work.Stems.sigmaA (1 : Fin 2) t) 0 = t 0 := rfl
theorem sigmaB_zero_other (t : IC 2) : (Work.Stems.sigmaB (1 : Fin 2) t) 0 = t 0 := rfl

theorem colAff_two_zero_sigmaA (t : IC 2) (ht : (t 0 : ℝ) ≤ 1/2) :
    colAff 2 (0 : Fin 2) (Work.Stems.sigmaA (0 : Fin 2) t) = t := by
  funext i
  rcases fin_two_cases i with h | h
  · rw [h]; apply Subtype.ext
    rw [colAff_apply, sigmaA_zero_coe,
      clamp_coe_of_mem ⟨by linarith [(t 0).2.1], by linarith [ht]⟩]
    rw [fin2_zero_coe, zero_add]; ring
  · rw [h]; simp only [colAff_apply_one, sigmaA_one_other]

theorem colAff_two_one_sigmaB (t : IC 2) (ht : 1/2 < (t 0 : ℝ)) :
    colAff 2 (1 : Fin 2) (Work.Stems.sigmaB (0 : Fin 2) t) = t := by
  funext i
  rcases fin_two_cases i with h | h
  · rw [h]; apply Subtype.ext
    rw [colAff_apply, sigmaB_zero_coe,
      clamp_coe_of_mem ⟨by linarith, by linarith [(t 0).2.2]⟩]
    rw [fin2_one_coe]; ring
  · rw [h]; simp only [colAff_apply_one, sigmaB_one_other]

theorem rowAff_two_zero_sigmaA (t : IC 2) (ht : (t 1 : ℝ) ≤ 1/2) :
    rowAff 2 (0 : Fin 2) (Work.Stems.sigmaA (1 : Fin 2) t) = t := by
  funext i
  rcases fin_two_cases i with h | h
  · rw [h]; simp only [rowAff_apply, sigmaA_zero_other]
  · rw [h]; apply Subtype.ext
    rw [rowAff_apply_one, sigmaA_one_coe,
      clamp_coe_of_mem ⟨by linarith [(t 1).2.1], by linarith [ht]⟩]
    rw [fin2_zero_coe, zero_add]; ring

theorem rowAff_two_one_sigmaB (t : IC 2) (ht : 1/2 < (t 1 : ℝ)) :
    rowAff 2 (1 : Fin 2) (Work.Stems.sigmaB (1 : Fin 2) t) = t := by
  funext i
  rcases fin_two_cases i with h | h
  · rw [h]; simp only [rowAff_apply, sigmaB_zero_other]
  · rw [h]; apply Subtype.ext
    rw [rowAff_apply_one, sigmaB_one_coe,
      clamp_coe_of_mem ⟨by linarith, by linarith [(t 1).2.2]⟩]
    rw [fin2_one_coe]; ring

/-- **The two-strip concatenation of the strip readings is the cube itself** (vertical case). -/
theorem transAt_vCube (q : GenLoop (Fin 2) X x₀)
    (h0 : ∀ y ∈ Cube.boundary (Fin 2), q.1 (colAff 2 (0:Fin 2) y) = x₀)
    (h1 : ∀ y ∈ Cube.boundary (Fin 2), q.1 (colAff 2 (1:Fin 2) y) = x₀) :
    GenLoop.transAt 0 (vCube q 2 (0:Fin 2) h0) (vCube q 2 (1:Fin 2) h1) = q := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  show (if (t 0 : ℝ) ≤ 1/2 then (vCube q 2 (0:Fin 2) h0) (Work.Stems.sigmaA (0:Fin 2) t)
    else (vCube q 2 (1:Fin 2) h1) (Work.Stems.sigmaB (0:Fin 2) t)) = q.1 t
  rw [vCube_apply_fun, vCube_apply_fun]
  by_cases ht : (t 0 : ℝ) ≤ 1/2
  · rw [if_pos ht, colAff_two_zero_sigmaA t ht]
  · rw [if_neg ht, colAff_two_one_sigmaB t (not_le.mp ht)]

/-- **The two-strip concatenation of the strip readings is the cube itself** (horizontal case). -/
theorem transAt_hCube (q : GenLoop (Fin 2) X x₀)
    (h0 : ∀ y ∈ Cube.boundary (Fin 2), q.1 (rowAff 2 (0:Fin 2) y) = x₀)
    (h1 : ∀ y ∈ Cube.boundary (Fin 2), q.1 (rowAff 2 (1:Fin 2) y) = x₀) :
    GenLoop.transAt 1 (hCube q 2 (0:Fin 2) h0) (hCube q 2 (1:Fin 2) h1) = q := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  show (if (t 1 : ℝ) ≤ 1/2 then (hCube q 2 (0:Fin 2) h0) (Work.Stems.sigmaA (1:Fin 2) t)
    else (hCube q 2 (1:Fin 2) h1) (Work.Stems.sigmaB (1:Fin 2) t)) = q.1 t
  rw [hCube_apply_fun, hCube_apply_fun]
  by_cases ht : (t 1 : ℝ) ≤ 1/2
  · rw [if_pos ht, rowAff_two_zero_sigmaA t ht]
  · rw [if_neg ht, rowAff_two_one_sigmaB t (not_le.mp ht)]

/-- The index of the middle line of the `2^(r+1)`-grid. -/
def midIdx (r : ℕ) : Fin (2^(r+1)) :=
  ⟨2^r, by
    have h2 : 0 < 2^r := pow_pos (by norm_num) r
    have h : 2^r < 2^r + 2^r := by omega
    rwa [powTwo_add r] at h⟩

theorem midIdx_val (r : ℕ) : ((midIdx r : ℕ) : ℝ) = 2^r := by simp [midIdx]

/-- The middle line of the `2^(r+1)`-grid, read vertically. -/
theorem mid_line_v {r : ℕ} {q : GenLoop (Fin 2) X x₀}
    (h : ∀ k : Fin (2^(r+1)), ∀ y ∈ Cube.boundary (Fin 2), q.1 (colAff (2^(r+1)) k y) = x₀)
    (s : unitInterval) : q.1 (pair2 halfPt s) = x₀ := by
  have hpt : pair2 halfPt s = colAff (2^(r+1)) (midIdx r) (pair2 0 s) := by
    funext i
    rcases fin_two_cases i with hi | hi
    · rw [hi]; apply Subtype.ext
      rw [pair2_zero, colAff_apply, pair2_zero, uI_zero_coe, halfPt_coe, midIdx_val]
      simp only [add_zero]
      rw [h2pow r]
      push_cast
      field_simp <;> ring
    · rw [hi]; simp only [colAff_apply_one, pair2_one]
  rw [hpt]
  exact h (midIdx r) (pair2 0 s) ⟨0, Or.inl rfl⟩

/-- The middle line of the `2^(r+1)`-grid, read horizontally. -/
theorem mid_line_h {r : ℕ} {q : GenLoop (Fin 2) X x₀}
    (h : ∀ k : Fin (2^(r+1)), ∀ y ∈ Cube.boundary (Fin 2), q.1 (rowAff (2^(r+1)) k y) = x₀)
    (s : unitInterval) : q.1 (pair2 s halfPt) = x₀ := by
  have hpt : pair2 s halfPt = rowAff (2^(r+1)) (midIdx r) (pair2 s 0) := by
    funext i
    rcases fin_two_cases i with hi | hi
    · rw [hi]; simp only [rowAff_apply, pair2_zero]
    · rw [hi]; apply Subtype.ext
      rw [pair2_one, rowAff_apply_one, pair2_one, uI_zero_coe, halfPt_coe, midIdx_val]
      simp only [add_zero]
      rw [h2pow r]
      push_cast
      field_simp <;> ring
  rw [hpt]
  exact h (midIdx r) (pair2 s 0) ⟨1, Or.inl rfl⟩

/-- **The two-strip vertical readings are based as soon as the full grid of vertical readings
is based.** -/
theorem vCube_halves {r : ℕ} {q : GenLoop (Fin 2) X x₀}
    (h : ∀ k : Fin (2^(r+1)), ∀ y ∈ Cube.boundary (Fin 2), q.1 (colAff (2^(r+1)) k y) = x₀) :
    (∀ y ∈ Cube.boundary (Fin 2), q.1 (colAff 2 (0 : Fin 2) y) = x₀) ∧
      (∀ y ∈ Cube.boundary (Fin 2), q.1 (colAff 2 (1 : Fin 2) y) = x₀) := by
  have hmid := mid_line_v h
  constructor
  · intro y hy
    rcases hy with ⟨i, hi | hi⟩
    · rcases fin_two_cases i with hh | hh
      · rw [hh] at hi
        rw [colAff_zero_eq_zero y hi]
        exact q.2 _ ⟨0, Or.inl rfl⟩
      · rw [hh] at hi
        have hy1 : (colAff 2 (0:Fin 2) y) 1 = 0 := by
          rw [colAff_apply_one]; exact hi
        exact q.2 _ ⟨1, Or.inl hy1⟩
    · rcases fin_two_cases i with hh | hh
      · rw [hh] at hi
        rw [colAff_zero_eq_half y hi]
        exact hmid (y 1)
      · rw [hh] at hi
        have hy1 : (colAff 2 (0:Fin 2) y) 1 = 1 := by
          rw [colAff_apply_one]; exact hi
        exact q.2 _ ⟨1, Or.inr hy1⟩
  · intro y hy
    rcases hy with ⟨i, hi | hi⟩
    · rcases fin_two_cases i with hh | hh
      · rw [hh] at hi
        rw [colAff_one_eq_half y hi]
        exact hmid (y 1)
      · rw [hh] at hi
        have hy1 : (colAff 2 (1:Fin 2) y) 1 = 0 := by
          rw [colAff_apply_one]; exact hi
        exact q.2 _ ⟨1, Or.inl hy1⟩
    · rcases fin_two_cases i with hh | hh
      · rw [hh] at hi
        rw [colAff_one_eq_one y hi]
        exact q.2 _ ⟨0, Or.inr rfl⟩
      · rw [hh] at hi
        have hy1 : (colAff 2 (1:Fin 2) y) 1 = 1 := by
          rw [colAff_apply_one]; exact hi
        exact q.2 _ ⟨1, Or.inr hy1⟩

/-- **The two-strip horizontal readings are based as soon as the full grid of horizontal readings
is based.** -/
theorem hCube_halves {r : ℕ} {q : GenLoop (Fin 2) X x₀}
    (h : ∀ k : Fin (2^(r+1)), ∀ y ∈ Cube.boundary (Fin 2), q.1 (rowAff (2^(r+1)) k y) = x₀) :
    (∀ y ∈ Cube.boundary (Fin 2), q.1 (rowAff 2 (0 : Fin 2) y) = x₀) ∧
      (∀ y ∈ Cube.boundary (Fin 2), q.1 (rowAff 2 (1 : Fin 2) y) = x₀) := by
  have hmid := mid_line_h h
  constructor
  · intro y hy
    rcases hy with ⟨i, hi | hi⟩
    · rcases fin_two_cases i with hh | hh
      · rw [hh] at hi
        rw [eq_pair2 (rowAff 2 (0:Fin 2) y), rowAff_apply, hi]
        exact q.2 _ ⟨0, Or.inl rfl⟩
      · rw [hh] at hi
        have hy1 : (rowAff 2 (0:Fin 2) y) 1 = 0 := by
          apply Subtype.ext
          simp only [rowAff_apply_one, fin2_zero_coe, hi, uI_zero_coe]
          norm_num
        exact q.2 _ ⟨1, Or.inl hy1⟩
    · rcases fin_two_cases i with hh | hh
      · rw [hh] at hi
        rw [eq_pair2 (rowAff 2 (0:Fin 2) y), rowAff_apply, hi]
        exact q.2 _ ⟨0, Or.inr rfl⟩
      · rw [hh] at hi
        have hy1 : (rowAff 2 (0:Fin 2) y) 1 = halfPt := by
          apply Subtype.ext
          simp only [rowAff_apply_one, fin2_zero_coe, halfPt_coe, hi, uI_one_coe]
          norm_num
        rw [eq_pair2 (rowAff 2 (0:Fin 2) y), rowAff_apply, hy1]
        exact hmid (y 0)
  · intro y hy
    rcases hy with ⟨i, hi | hi⟩
    · rcases fin_two_cases i with hh | hh
      · rw [hh] at hi
        rw [eq_pair2 (rowAff 2 (1:Fin 2) y), rowAff_apply, hi]
        exact q.2 _ ⟨0, Or.inl rfl⟩
      · rw [hh] at hi
        have hy1 : (rowAff 2 (1:Fin 2) y) 1 = halfPt := by
          apply Subtype.ext
          simp only [rowAff_apply_one, fin2_one_coe, halfPt_coe, hi, uI_zero_coe]
          norm_num
        rw [eq_pair2 (rowAff 2 (1:Fin 2) y), rowAff_apply, hy1]
        exact hmid (y 0)
    · rcases fin_two_cases i with hh | hh
      · rw [hh] at hi
        rw [eq_pair2 (rowAff 2 (1:Fin 2) y), rowAff_apply, hi]
        exact q.2 _ ⟨0, Or.inr rfl⟩
      · rw [hh] at hi
        have hy1 : (rowAff 2 (1:Fin 2) y) 1 = 1 := by
          apply Subtype.ext
          simp only [rowAff_apply_one, fin2_one_coe, hi, uI_one_coe]
          norm_num
        exact q.2 _ ⟨1, Or.inr hy1⟩

/-! ## The reindexing lemmas -/

theorem vCube_comp_zero (r : ℕ) (j : Fin (2^r)) (q : GenLoop (Fin 2) X x₀)
    (h0 : ∀ y ∈ Cube.boundary (Fin 2), q.1 (colAff 2 (0:Fin 2) y) = x₀)
    (h : ∀ y ∈ Cube.boundary (Fin 2), q.1 (colAff (2^(r+1)) (halfA r j) y) = x₀)
    (hA : ∀ y ∈ Cube.boundary (Fin 2), (vCube q 2 (0:Fin 2) h0).1 (colAff (2^r) j y) = x₀) :
    vCube q (2^(r+1)) (halfA r j) h = vCube (vCube q 2 (0:Fin 2) h0) (2^r) j hA := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  simp only [vCube_apply]
  rw [colAff_comp_zero]

theorem vCube_comp_one (r : ℕ) (j : Fin (2^r)) (q : GenLoop (Fin 2) X x₀)
    (h0 : ∀ y ∈ Cube.boundary (Fin 2), q.1 (colAff 2 (1:Fin 2) y) = x₀)
    (h : ∀ y ∈ Cube.boundary (Fin 2), q.1 (colAff (2^(r+1)) (halfB r j) y) = x₀)
    (hA : ∀ y ∈ Cube.boundary (Fin 2), (vCube q 2 (1:Fin 2) h0).1 (colAff (2^r) j y) = x₀) :
    vCube q (2^(r+1)) (halfB r j) h = vCube (vCube q 2 (1:Fin 2) h0) (2^r) j hA := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  simp only [vCube_apply]
  rw [colAff_comp_one]

theorem hCube_comp_zero (r : ℕ) (j : Fin (2^r)) (q : GenLoop (Fin 2) X x₀)
    (h0 : ∀ y ∈ Cube.boundary (Fin 2), q.1 (rowAff 2 (0:Fin 2) y) = x₀)
    (h : ∀ y ∈ Cube.boundary (Fin 2), q.1 (rowAff (2^(r+1)) (halfA r j) y) = x₀)
    (hA : ∀ y ∈ Cube.boundary (Fin 2), (hCube q 2 (0:Fin 2) h0).1 (rowAff (2^r) j y) = x₀) :
    hCube q (2^(r+1)) (halfA r j) h = hCube (hCube q 2 (0:Fin 2) h0) (2^r) j hA := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  simp only [hCube_apply]
  rw [rowAff_comp_zero]

theorem hCube_comp_one (r : ℕ) (j : Fin (2^r)) (q : GenLoop (Fin 2) X x₀)
    (h0 : ∀ y ∈ Cube.boundary (Fin 2), q.1 (rowAff 2 (1:Fin 2) y) = x₀)
    (h : ∀ y ∈ Cube.boundary (Fin 2), q.1 (rowAff (2^(r+1)) (halfB r j) y) = x₀)
    (hA : ∀ y ∈ Cube.boundary (Fin 2), (hCube q 2 (1:Fin 2) h0).1 (rowAff (2^r) j y) = x₀) :
    hCube q (2^(r+1)) (halfB r j) h = hCube (hCube q 2 (1:Fin 2) h0) (2^r) j hA := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  simp only [hCube_apply]
  rw [rowAff_comp_one]

/-! ## The subdivision -/

/-- **The balanced nested arrangement of the vertical strip readings of `q` is `q` itself.** -/
theorem bArr_vCube (r : ℕ) : ∀ (q : GenLoop (Fin 2) X x₀)
    (h : ∀ k : Fin (2^r), ∀ y ∈ Cube.boundary (Fin 2), q.1 (colAff (2^r) k y) = x₀),
    bArr 0 r (fun k => vCube q (2^r) k (h k)) = q := by
  induction r with
  | zero =>
      intro q h
      apply Subtype.ext
      rw [bArr_zero]
      apply ContinuousMap.ext
      intro y
      show q.1 (colAff 1 (0:Fin 1) y) = q.1 y
      rw [colAff_one]
  | succ r ih =>
      intro q h
      have hA : ∀ y ∈ Cube.boundary (Fin 2), q.1 (colAff 2 (0:Fin 2) y) = x₀ :=
        (vCube_halves h).1
      have hB : ∀ y ∈ Cube.boundary (Fin 2), q.1 (colAff 2 (1:Fin 2) y) = x₀ :=
        (vCube_halves h).2
      have hA' : ∀ j : Fin (2^r), ∀ y ∈ Cube.boundary (Fin 2),
          (vCube q 2 (0:Fin 2) hA).1 (colAff (2^r) j y) = x₀ := by
        intro j y hy
        rw [vCube_apply, colAff_comp_zero]
        exact h (halfA r j) y hy
      have hB' : ∀ j : Fin (2^r), ∀ y ∈ Cube.boundary (Fin 2),
          (vCube q 2 (1:Fin 2) hB).1 (colAff (2^r) j y) = x₀ := by
        intro j y hy
        rw [vCube_apply, colAff_comp_one]
        exact h (halfB r j) y hy
      have e1 : bArr 0 r ((fun k => vCube q (2^(r+1)) k (h k)) ∘ halfA r)
          = vCube q 2 (0:Fin 2) hA := by
        rw [show ((fun k => vCube q (2^(r+1)) k (h k)) ∘ halfA r)
            = (fun j => vCube (vCube q 2 (0:Fin 2) hA) (2^r) j (hA' j)) from by
          funext j
          exact vCube_comp_zero r j q hA (h (halfA r j)) (hA' j)]
        exact ih (vCube q 2 (0:Fin 2) hA) hA'
      have e2 : bArr 0 r ((fun k => vCube q (2^(r+1)) k (h k)) ∘ halfB r)
          = vCube q 2 (1:Fin 2) hB := by
        rw [show ((fun k => vCube q (2^(r+1)) k (h k)) ∘ halfB r)
            = (fun j => vCube (vCube q 2 (1:Fin 2) hB) (2^r) j (hB' j)) from by
          funext j
          exact vCube_comp_one r j q hB (h (halfB r j)) (hB' j)]
        exact ih (vCube q 2 (1:Fin 2) hB) hB'
      rw [bArr_succ 0, e1, e2]
      exact transAt_vCube q hA hB

/-- **The balanced nested arrangement of the horizontal strip readings of `q` is `q` itself.** -/
theorem bArr_hCube (r : ℕ) : ∀ (q : GenLoop (Fin 2) X x₀)
    (h : ∀ k : Fin (2^r), ∀ y ∈ Cube.boundary (Fin 2), q.1 (rowAff (2^r) k y) = x₀),
    bArr 1 r (fun k => hCube q (2^r) k (h k)) = q := by
  induction r with
  | zero =>
      intro q h
      apply Subtype.ext
      rw [bArr_zero]
      apply ContinuousMap.ext
      intro y
      show q.1 (rowAff 1 (0:Fin 1) y) = q.1 y
      rw [rowAff_one]
  | succ r ih =>
      intro q h
      have hA : ∀ y ∈ Cube.boundary (Fin 2), q.1 (rowAff 2 (0:Fin 2) y) = x₀ :=
        (hCube_halves h).1
      have hB : ∀ y ∈ Cube.boundary (Fin 2), q.1 (rowAff 2 (1:Fin 2) y) = x₀ :=
        (hCube_halves h).2
      have hA' : ∀ j : Fin (2^r), ∀ y ∈ Cube.boundary (Fin 2),
          (hCube q 2 (0:Fin 2) hA).1 (rowAff (2^r) j y) = x₀ := by
        intro j y hy
        rw [hCube_apply, rowAff_comp_zero]
        exact h (halfA r j) y hy
      have hB' : ∀ j : Fin (2^r), ∀ y ∈ Cube.boundary (Fin 2),
          (hCube q 2 (1:Fin 2) hB).1 (rowAff (2^r) j y) = x₀ := by
        intro j y hy
        rw [hCube_apply, rowAff_comp_one]
        exact h (halfB r j) y hy
      have e1 : bArr 1 r ((fun k => hCube q (2^(r+1)) k (h k)) ∘ halfA r)
          = hCube q 2 (0:Fin 2) hA := by
        rw [show ((fun k => hCube q (2^(r+1)) k (h k)) ∘ halfA r)
            = (fun j => hCube (hCube q 2 (0:Fin 2) hA) (2^r) j (hA' j)) from by
          funext j
          exact hCube_comp_zero r j q hA (h (halfA r j)) (hA' j)]
        exact ih (hCube q 2 (0:Fin 2) hA) hA'
      have e2 : bArr 1 r ((fun k => hCube q (2^(r+1)) k (h k)) ∘ halfB r)
          = hCube q 2 (1:Fin 2) hB := by
        rw [show ((fun k => hCube q (2^(r+1)) k (h k)) ∘ halfB r)
            = (fun j => hCube (hCube q 2 (1:Fin 2) hB) (2^r) j (hB' j)) from by
          funext j
          exact hCube_comp_one r j q hB (h (halfB r j)) (hB' j)]
        exact ih (hCube q 2 (1:Fin 2) hB) hB'
      rw [bArr_succ 1, e1, e2]
      exact transAt_hCube q hA hB

/-- **The subdivision formula**: the class of `q` is the product of the classes of its `2^r`
vertical strip readings. -/
theorem cl_eq_prod_vCube (r : ℕ) (q : GenLoop (Fin 2) X x₀)
    (h : ∀ k : Fin (2^r), ∀ y ∈ Cube.boundary (Fin 2), q.1 (colAff (2^r) k y) = x₀) :
    cl x₀ q = ∏ k : Fin (2^r), cl x₀ (vCube q (2^r) k (h k)) := by
  rw [← bArr_class r 0 (fun k => vCube q (2^r) k (h k)), bArr_vCube r q h]

/-- **The subdivision formula**: the class of `q` is the product of the classes of its `2^r`
horizontal strip readings. -/
theorem cl_eq_prod_hCube (r : ℕ) (q : GenLoop (Fin 2) X x₀)
    (h : ∀ k : Fin (2^r), ∀ y ∈ Cube.boundary (Fin 2), q.1 (rowAff (2^r) k y) = x₀) :
    cl x₀ q = ∏ k : Fin (2^r), cl x₀ (hCube q (2^r) k (h k)) := by
  rw [← bArr_class r 1 (fun k => hCube q (2^r) k (h k)), bArr_hCube r q h]

/-! ## From the cell hypothesis to the strip hypotheses -/

/-- Every element of `I` is of the form `(j + u)/8` with `j : Fin 8`. -/
theorem exists_eighth (s : unitInterval) :
    ∃ (j : Fin 8) (u : unitInterval), (s:ℝ) = ((j:ℝ) + (u:ℝ))/8 := by
  rcases le_or_gt (8 * (s:ℝ)) 7 with h | h
  · set j : ℕ := ⌊8 * (s:ℝ)⌋₊ with hj
    have h0 : (0:ℝ) ≤ 8 * (s:ℝ) := by have := s.2.1; linarith
    have hjle : (j:ℝ) ≤ 8 * (s:ℝ) := Nat.floor_le h0
    have hjlt : 8 * (s:ℝ) < (j:ℝ) + 1 := Nat.lt_floor_add_one _
    have hj7 : j ≤ 7 := by
      have h7 : (j:ℝ) ≤ 7 := by linarith
      exact_mod_cast h7
    refine ⟨⟨j, by omega⟩, ⟨8 * (s:ℝ) - j, ⟨by linarith, by linarith⟩⟩, ?_⟩
    push_cast
    ring
  · refine ⟨7, ⟨8 * (s:ℝ) - 7, ⟨by have := s.2.1; linarith, by have := s.2.2; linarith⟩⟩, ?_⟩
    push_cast
    norm_num

/-- The left edge of the `(i,j)`-cell reads the vertical line through `gLine i`. -/
theorem cellRead_left (i j : Fin 8) (s : unitInterval) (u : unitInterval)
    (hu : (s:ℝ) = ((j:ℝ) + (u:ℝ))/8) :
    pair2 (gLine i.castSucc) s = cellRead i j (pair2 0 u) := by
  have hmem : (1/8) * (u:ℝ) + ((j:ℕ):ℝ)/8 ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · have h1 := u.2.1
      have h2 : (0:ℝ) ≤ ((j:ℕ):ℝ) := Nat.cast_nonneg _
      linarith
    · have hj : ((j:ℕ):ℝ) + 1 ≤ 8 := by have h := j.isLt; exact_mod_cast h
      have hu1 := u.2.2
      linarith
  funext t
  rcases fin_two_cases t with ht | ht
  · rw [ht]
    exact (cellRead_coord0_zero i j (pair2 0 u) rfl).symm
  · rw [ht]
    apply Subtype.ext
    rw [show ((cellRead i j (pair2 0 u)) 1 : ℝ)
        = clamp ((1/8) * ((pair2 0 u) 1 : ℝ) + ((j:ℕ):ℝ)/8) from rfl]
    rw [pair2_one, pair2_one, clamp_coe_of_mem hmem]
    rw [hu]; ring

/-- The bottom edge of the `(i,j)`-cell reads the horizontal line through `gLine j`. -/
theorem cellRead_bot (i j : Fin 8) (s : unitInterval) (u : unitInterval)
    (hu : (s:ℝ) = ((i:ℝ) + (u:ℝ))/8) :
    pair2 s (gLine j.castSucc) = cellRead i j (pair2 u 0) := by
  have hmem : (1/8) * (u:ℝ) + ((i:ℕ):ℝ)/8 ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · have h1 := u.2.1
      have h2 : (0:ℝ) ≤ ((i:ℕ):ℝ) := Nat.cast_nonneg _
      linarith
    · have hi : ((i:ℕ):ℝ) + 1 ≤ 8 := by have h := i.isLt; exact_mod_cast h
      have hu1 := u.2.2
      linarith
  funext t
  rcases fin_two_cases t with ht | ht
  · rw [ht]
    apply Subtype.ext
    rw [show ((cellRead i j (pair2 u 0)) 0 : ℝ)
        = clamp ((1/8) * ((pair2 u 0) 0 : ℝ) + ((i:ℕ):ℝ)/8) from rfl]
    rw [pair2_zero, pair2_zero, clamp_coe_of_mem hmem]
    rw [hu]; ring
  · rw [ht]
    exact (cellRead_coord1_zero i j (pair2 u 0) rfl).symm

/-- **From the cell hypothesis to the full vertical lines.** -/
theorem line_vanish_v (p : GenLoop (Fin 2) X x₀)
    (hbound : ∀ (c : Fin 8 × Fin 8) (y : IC 2), y ∈ Cube.boundary (Fin 2) →
      p.1 (cellRead c.1 c.2 y) = x₀) :
    ∀ (k : Fin 9) (s : unitInterval), p.1 (pair2 (gLine k) s) = x₀ := by
  intro k s
  have hk9 : (k:ℕ) ≤ 8 := by have := k.isLt; omega
  rcases eq_or_ne (k : ℕ) 0 with hk0 | hk0
  · have hgl : gLine k = 0 := by
      apply Subtype.ext; rw [gLine_coe, hk0]; norm_num
    rw [hgl]; exact p.2 _ ⟨0, Or.inl rfl⟩
  rcases eq_or_ne (k : ℕ) 8 with hk8 | hk8
  · have hgl : gLine k = 1 := by
      apply Subtype.ext; rw [gLine_coe, hk8]; norm_num
    rw [hgl]; exact p.2 _ ⟨0, Or.inr rfl⟩
  · obtain ⟨j, u, hu⟩ := exists_eighth s
    have hgl : gLine k = gLine (⟨(k:ℕ), by omega⟩ : Fin 8).castSucc := by
      congr 1
    rw [hgl, cellRead_left ⟨(k:ℕ), by omega⟩ j s u hu]
    exact hbound (⟨(k:ℕ), by omega⟩, j) (pair2 0 u) ⟨0, Or.inl rfl⟩

/-- **From the cell hypothesis to the full horizontal lines.** -/
theorem line_vanish_h (p : GenLoop (Fin 2) X x₀)
    (hbound : ∀ (c : Fin 8 × Fin 8) (y : IC 2), y ∈ Cube.boundary (Fin 2) →
      p.1 (cellRead c.1 c.2 y) = x₀) :
    ∀ (k : Fin 9) (s : unitInterval), p.1 (pair2 s (gLine k)) = x₀ := by
  intro k s
  have hk9 : (k:ℕ) ≤ 8 := by have := k.isLt; omega
  rcases eq_or_ne (k : ℕ) 0 with hk0 | hk0
  · have hgl : gLine k = 0 := by
      apply Subtype.ext; rw [gLine_coe, hk0]; norm_num
    rw [hgl]; exact p.2 _ ⟨1, Or.inl rfl⟩
  rcases eq_or_ne (k : ℕ) 8 with hk8 | hk8
  · have hgl : gLine k = 1 := by
      apply Subtype.ext; rw [gLine_coe, hk8]; norm_num
    rw [hgl]; exact p.2 _ ⟨1, Or.inr rfl⟩
  · obtain ⟨i, u, hu⟩ := exists_eighth s
    have hgl : gLine k = gLine (⟨(k:ℕ), by omega⟩ : Fin 8).castSucc := by
      congr 1
    rw [hgl, cellRead_bot i ⟨(k:ℕ), by omega⟩ s u hu]
    exact hbound (i, ⟨(k:ℕ), by omega⟩) (pair2 u 0) ⟨1, Or.inl rfl⟩

/-- **From the vertical lines to the basedness of the eight vertical strip readings.** -/
theorem cube_hyp_v (p : GenLoop (Fin 2) X x₀)
    (hV : ∀ (k : Fin 9) (s : unitInterval), p.1 (pair2 (gLine k) s) = x₀) :
    ∀ (k : Fin 8) (y : IC 2), y ∈ Cube.boundary (Fin 2) → p.1 (colAff 8 k y) = x₀ := by
  intro k y hy
  rcases hy with ⟨i, hi | hi⟩
  · rcases fin_two_cases i with hh | hh
    · rw [hh] at hi
      have hpt : colAff 8 k y = pair2 (gLine k.castSucc) (y 1) := by
        funext t
        rcases fin_two_cases t with ht | ht
        · rw [ht]; apply Subtype.ext
          rw [pair2_zero, colAff_apply, hi, uI_zero_coe, gLine_coe, Fin.val_castSucc]
          norm_num
        · rw [ht]; simp only [pair2_one, colAff_apply_one]
      rw [hpt]
      exact hV k.castSucc (y 1)
    · rw [hh] at hi
      have h1 : (colAff 8 k y) 1 = 0 := by rw [colAff_apply_one]; exact hi
      exact p.2 _ ⟨1, Or.inl h1⟩
  · rcases fin_two_cases i with hh | hh
    · rw [hh] at hi
      have hpt : colAff 8 k y = pair2 (gLine k.succ) (y 1) := by
        funext t
        rcases fin_two_cases t with ht | ht
        · rw [ht]; apply Subtype.ext
          rw [pair2_zero, colAff_apply, hi, uI_one_coe, gLine_coe, Fin.val_succ]
          push_cast; ring
        · rw [ht]; simp only [pair2_one, colAff_apply_one]
      rw [hpt]
      exact hV k.succ (y 1)
    · rw [hh] at hi
      have h1 : (colAff 8 k y) 1 = 1 := by rw [colAff_apply_one]; exact hi
      exact p.2 _ ⟨1, Or.inr h1⟩

/-- **From the horizontal lines to the basedness of the eight horizontal strip readings.** -/
theorem cube_hyp_h (p : GenLoop (Fin 2) X x₀)
    (hH : ∀ (k : Fin 9) (s : unitInterval), p.1 (pair2 s (gLine k)) = x₀) :
    ∀ (k : Fin 8) (y : IC 2), y ∈ Cube.boundary (Fin 2) → p.1 (rowAff 8 k y) = x₀ := by
  intro k y hy
  rcases hy with ⟨i, hi | hi⟩
  · rcases fin_two_cases i with hh | hh
    · rw [hh] at hi
      have h0 : (rowAff 8 k y) 0 = 0 := by rw [rowAff_apply]; exact hi
      exact p.2 _ ⟨0, Or.inl h0⟩
    · rw [hh] at hi
      have h2 : (rowAff 8 k y) 1 = gLine k.castSucc := by
        apply Subtype.ext
        rw [rowAff_apply_one, hi, uI_zero_coe, gLine_coe, Fin.val_castSucc]
        norm_num
      have hpt : rowAff 8 k y = pair2 (y 0) (gLine k.castSucc) := by
        funext t
        rcases fin_two_cases t with ht | ht
        · rw [ht]; simp only [rowAff_apply, pair2_zero]
        · rw [ht]; simp only [pair2_one, h2]
      rw [hpt]
      exact hH k.castSucc (y 0)
  · rcases fin_two_cases i with hh | hh
    · rw [hh] at hi
      have h0 : (rowAff 8 k y) 0 = 1 := by rw [rowAff_apply]; exact hi
      exact p.2 _ ⟨0, Or.inr h0⟩
    · rw [hh] at hi
      have h2 : (rowAff 8 k y) 1 = gLine k.succ := by
        apply Subtype.ext
        rw [rowAff_apply_one, hi, uI_one_coe, gLine_coe, Fin.val_succ]
        push_cast; ring
      have hpt : rowAff 8 k y = pair2 (y 0) (gLine k.succ) := by
        funext t
        rcases fin_two_cases t with ht | ht
        · rw [ht]; simp only [rowAff_apply, pair2_zero]
        · rw [ht]; simp only [pair2_one, h2]
      rw [hpt]
      exact hH k.succ (y 0)

/-- The `(i,k)`-cell reading is the `k`-th horizontal strip reading of the `i`-th vertical strip
reading. -/
theorem colAff_rowAff (i k : Fin 8) (y : IC 2) :
    colAff 8 i (rowAff 8 k y) = cellRead i k y := by
  have hmi : (1/8) * (y 0 : ℝ) + ((i:ℕ):ℝ)/8 ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · have h1 := (y 0).2.1
      have h2 : (0:ℝ) ≤ ((i:ℕ):ℝ) := Nat.cast_nonneg _
      linarith
    · have hi : ((i:ℕ):ℝ) + 1 ≤ 8 := by have h := i.isLt; exact_mod_cast h
      have hy1 := (y 0).2.2
      linarith
  have hmk : (1/8) * (y 1 : ℝ) + ((k:ℕ):ℝ)/8 ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · have h1 := (y 1).2.1
      have h2 : (0:ℝ) ≤ ((k:ℕ):ℝ) := Nat.cast_nonneg _
      linarith
    · have hk : ((k:ℕ):ℝ) + 1 ≤ 8 := by have h := k.isLt; exact_mod_cast h
      have hy1 := (y 1).2.2
      linarith
  funext t
  rcases fin_two_cases t with ht | ht
  · rw [ht]; apply Subtype.ext
    rw [colAff_apply, rowAff_apply]
    rw [show ((cellRead i k y) 0 : ℝ)
        = clamp ((1/8) * (y 0 : ℝ) + ((i:ℕ):ℝ)/8) from rfl]
    rw [clamp_coe_of_mem hmi]
    ring
  · rw [ht]; apply Subtype.ext
    rw [colAff_apply_one, rowAff_apply_one]
    rw [show ((cellRead i k y) 1 : ℝ)
        = clamp ((1/8) * (y 1 : ℝ) + ((k:ℕ):ℝ)/8) from rfl]
    rw [clamp_coe_of_mem hmk]
    ring

/-- The horizontal hypothesis for the horizontal subdivision of the `i`-th column reading. -/
theorem hCube_hyp_of_cells (p : GenLoop (Fin 2) X x₀)
    (hv : ∀ (k : Fin 8) (y : IC 2), y ∈ Cube.boundary (Fin 2) → p.1 (colAff 8 k y) = x₀)
    (hbound : ∀ (c : Fin 8 × Fin 8) (y : IC 2), y ∈ Cube.boundary (Fin 2) →
      p.1 (cellRead c.1 c.2 y) = x₀)
    (i : Fin 8) :
    ∀ k : Fin 8, ∀ y ∈ Cube.boundary (Fin 2), (vCube p 8 i (hv i)).1 (rowAff 8 k y) = x₀ := by
  intro k y hy
  rw [vCube_apply, colAff_rowAff i k y]
  exact hbound (i, k) y hy

/-- The `k`-th horizontal strip reading of the `i`-th column reading is the `(i,k)`-cell reading. -/
theorem hCube_eq_cellCube (p : GenLoop (Fin 2) X x₀)
    (hv : ∀ (k : Fin 8) (y : IC 2), y ∈ Cube.boundary (Fin 2) → p.1 (colAff 8 k y) = x₀)
    (hbound : ∀ (c : Fin 8 × Fin 8) (y : IC 2), y ∈ Cube.boundary (Fin 2) →
      p.1 (cellRead c.1 c.2 y) = x₀)
    (i k : Fin 8) :
    hCube (vCube p 8 i (hv i)) 8 k (hCube_hyp_of_cells p hv hbound i k)
      = cellCube p i k (hbound (i, k)) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  show (vCube p 8 i (hv i)).1 (rowAff 8 k y) = (compGenLoop (hbound (i, k))).1 y
  rw [vCube_apply, colAff_rowAff]
  rfl

end

end Grid8

open Grid8 in
/-- **The `8 × 8` grid subdivision of a based `2`-cube.** -/
theorem cl_grid8 {X : Type} [TopologicalSpace X] {x₀ : X} (p : GenLoop (Fin 2) X x₀)
    (hbound : ∀ (c : Fin 8 × Fin 8) (y : Work.Stems.Cubical.IC 2), y ∈ Cube.boundary (Fin 2) →
      p.1 ((Work.Stems.Hur2b.cellRead c.1 c.2) y) = x₀) :
    Work.Stems.Hur2b.cl x₀ p = ∏ c : Fin 8 × Fin 8,
      Work.Stems.Hur2b.cl x₀ (Work.Stems.Hur2b.cellCube p c.1 c.2 (hbound c)) := by
  classical
  have hV := line_vanish_v p hbound
  have hH := line_vanish_h p hbound
  have hv := cube_hyp_v p hV
  have hh := cube_hyp_h p hH
  have hinner : ∀ i : Fin 8, cl x₀ (vCube p 8 i (hv i))
      = ∏ k : Fin 8, cl x₀ (hCube (vCube p 8 i (hv i)) 8 k
          (hCube_hyp_of_cells p hv hbound i k)) :=
    fun i => cl_eq_prod_hCube 3 _ (hCube_hyp_of_cells p hv hbound i)
  calc cl x₀ p = ∏ i : Fin 8, cl x₀ (vCube p 8 i (hv i)) := cl_eq_prod_vCube 3 p hv
    _ = ∏ i : Fin 8, ∏ k : Fin 8, cl x₀ (hCube (vCube p 8 i (hv i)) 8 k
          (hCube_hyp_of_cells p hv hbound i k)) := Finset.prod_congr rfl (fun i _ => hinner i)
    _ = ∏ i : Fin 8, ∏ k : Fin 8, cl x₀ (cellCube p i k (hbound (i, k))) := by
        apply Finset.prod_congr rfl
        intro i _
        apply Finset.prod_congr rfl
        intro k _
        rw [hCube_eq_cellCube p hv hbound i k]
    _ = ∏ c : Fin 8 × Fin 8, cl x₀ (cellCube p c.1 c.2 (hbound c)) := by
        rw [Fintype.prod_prod_type]

end Work.Stems.Hur2b
