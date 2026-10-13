/-
  WilC4/ulpm_BxDefs : the vocabulary of the crossing family `Bx` of `Work.WilC4.ulpm_Bx`.

  Given a `∅`-definable family `Y ⊆ ℝ^{k+2}` of graphs with doubling ratio `RatW Y c x w` and a set
  `E ⊆ ℝ`, the *crossing family* `Bx Y E ⊆ ℝ^{k+1}` consists of the points `(c,x)` at which,
  for some `m ∈ Mid E`, `x` is a boundary point (`Work.WilC2.IsBnd`) of the level set

      `Sfib Y c m = {x | ∃ w, RatW Y c x w ∧ w = m}`.

  Off `Bx Y E` the level sets are (by `Work.WilC4.bnd_interval_dichotomy`) all-or-nothing on every
  interval, which is what turns the monotonicity hypothesis of `ulpm_Bx` into the dichotomy of
  its conclusion.

  The file also fixes the *parametrised* level set `Sfam Y ⊆ ℝ^{k+2}` (coordinate `0` the point,
  coordinates `1, …, k` the parameters `c`, the last coordinate the value `m`), for which
  `Pfib1 (Sfam Y) p = Sfib Y (cOfF p) (mOfF p)`; `Sfam` is the input of
  `Work.WilC4.paramBnd_definable` producing the `∅`-definability of `Bx`, and the fibre of `Sfam`
  at a fixed `(c,m)` is the input of the o-minimality of `Work.WilC4.oMin_structure` producing
  the uniform finiteness of the fibres of `Bx`.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ULPMB
import Submission.Work.WilC4.ulpm_mono_param
import Submission.Work.WilC4.bnd_interval_dichotomy

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

variable {k : ℕ}

/-! ## 1. Reading the parameters off a tuple -/

/-- The `c`-coordinates of a tuple `u : Fin (k+2) → ℝ`: coordinate `0` is the point, coordinates
`1, …, k` are the parameters `c`, the last coordinate is the value `m`. -/
def cOfF (u : Fin (k + 2) → ℝ) : Fin k → ℝ := fun i => u (Fin.succ (Fin.castSucc i))

/-- The last coordinate of a tuple `u : Fin (k+2) → ℝ` (the value `m`). -/
def mOfF (u : Fin (k + 2) → ℝ) : ℝ := u (Fin.last (k + 1))

/-- The `c`-coordinates of a tuple `v : Fin (k+1) → ℝ`: coordinate `0` is the point. -/
def cOf (v : Fin (k + 1) → ℝ) : Fin k → ℝ := fun i => v i.succ

@[simp] lemma cOf_cons (x : ℝ) (c : Fin k → ℝ) : cOf (Fin.cons x c) = c := by
  funext i; simp [cOf]

@[simp] lemma cOfF_cons_tail (p : Fin (k + 2) → ℝ) (z : ℝ) :
    cOfF (Fin.cons z (Fin.tail p)) = cOfF p := by
  funext i; simp [cOfF, Fin.tail]

@[simp] lemma mOfF_cons_tail (p : Fin (k + 2) → ℝ) (z : ℝ) :
    mOfF (Fin.cons z (Fin.tail p)) = mOfF p := by
  simp [mOfF, Fin.tail]

/-! ## 2. The level sets and the crossing family -/

/-- `Sfib Y c m` : the set of `x` at which the doubling ratio takes the value `m`. -/
def Sfib (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (m : ℝ) : Set ℝ :=
  {x | ∃ w : ℝ, RatW Y c x w ∧ w = m}

/-- `Sfam Y` : the parametrised level set: coordinate `0` is the point `x`, coordinates `1, …, k`
are the parameters `c` and the last coordinate is the value `m`. -/
def Sfam (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 2) → ℝ) :=
  {u | ∃ w : ℝ, RatW Y (cOfF u) (u 0) w ∧ w = mOfF u}

/-- The fibre of the parametrised set `Sfam Y` over the parameter tuple `p` is the level set at
`(p 0, cOfF p, mOfF p)`. -/
@[simp] lemma Pfib1_Sfam (Y : Set (Fin (k + 2) → ℝ)) (p : Fin (k + 2) → ℝ) :
    Pfib1 (Sfam Y) p = Sfib Y (cOfF p) (mOfF p) := by
  ext z
  simp only [Pfib1, Sfib, Set.mem_setOf_eq, Sfam, Fin.cons_zero]
  constructor
  · rintro ⟨w, hw, hwm⟩; exact ⟨w, hw, hwm⟩
  · rintro ⟨w, hw, hwm⟩; exact ⟨w, hw, hwm⟩

/-- **The crossing family.**  `(c,x) ∈ Bx Y E` when, for some `m ∈ Mid E`, `x` is a boundary
point of the level set `Sfib Y c m`. -/
def Bx (Y : Set (Fin (k + 2) → ℝ)) (E : Set ℝ) : Set (Fin (k + 1) → ℝ) :=
  {v | ∃ m : ℝ, m ∈ Mid E ∧ WilC2.IsBnd (Sfib Y (cOf v) m) (v 0)}

/-- The fibre of the crossing family. -/
theorem mem_Bx_iff (Y : Set (Fin (k + 2) → ℝ)) (E : Set ℝ) (c : Fin k → ℝ) (x : ℝ) :
    Fin.cons x c ∈ Bx Y E ↔ ∃ m : ℝ, m ∈ Mid E ∧ WilC2.IsBnd (Sfib Y c m) x := by
  simp only [Bx, Set.mem_setOf_eq, cOf_cons, Fin.cons_zero]

/-! ## 3. The definability of `Bx` -/

/-- The set whose `∅`-definability `paramBnd_definable` produces: the boundary points of the
parametrised level sets, with the value `m` required to lie in `Mid E`. -/
def CrossSet (Y : Set (Fin (k + 2) → ℝ)) (E : Set ℝ) : Set (Fin (k + 2) → ℝ) :=
  {p | WilC2.IsBnd (Pfib1 (Sfam Y) p) (p 0)} ∩ {p | mOfF p ∈ Mid E}

/-- The reindexing putting the value `m` (the last coordinate of a tuple on `Fin (k+2)`) into the
second block of `Fin (k+1) ⊕ Fin 1`. -/
def e2f (k : ℕ) : Fin (k + 2) → Fin (k + 1) ⊕ Fin 1 :=
  Fin.lastCases (Sum.inr 0) (fun j : Fin (k + 1) => Sum.inl j)

@[simp] lemma cOfF_e2f (v : Fin (k + 1) → ℝ) (u : Fin 1 → ℝ) :
    cOfF ((Sum.elim v u) ∘ e2f k) = cOf v := by
  funext i
  simp only [cOfF, cOf, Function.comp_apply, e2f, Fin.succ_castSucc, Fin.lastCases_castSucc,
    Sum.elim_inl]

@[simp] lemma mOfF_e2f (v : Fin (k + 1) → ℝ) (u : Fin 1 → ℝ) :
    mOfF ((Sum.elim v u) ∘ e2f k) = u 0 := by
  simp only [mOfF, Function.comp_apply, e2f, Fin.lastCases_last, Sum.elim_inr]

@[simp] lemma zero_e2f (v : Fin (k + 1) → ℝ) (u : Fin 1 → ℝ) :
    ((Sum.elim v u) ∘ e2f k) 0 = v 0 := by
  show (Sum.elim v u) (e2f k (Fin.castSucc (0 : Fin (k + 1)))) = v 0
  simp only [Function.comp_apply, e2f, Fin.lastCases_castSucc, Sum.elim_inl]

/-- `Bx` as the projection of `CrossSet` along `e2f`: this is the shape on which
`Set.Definable.exists_of_finite` acts. -/
def BxProj (Y : Set (Fin (k + 2) → ℝ)) (E : Set ℝ) : Set (Fin (k + 1) → ℝ) :=
  {v | ∃ u : Fin 1 → ℝ, Sum.elim v u ∈
    (fun g : (Fin (k + 1) ⊕ Fin 1) → ℝ => g ∘ e2f k) ⁻¹' CrossSet Y E}

/-- `Bx` is the projection of the parametrised crossing set. -/
theorem Bx_eq_BxProj (Y : Set (Fin (k + 2) → ℝ)) (E : Set ℝ) : Bx Y E = BxProj Y E := by
  ext v
  simp only [Bx, BxProj, Set.mem_setOf_eq, Set.mem_preimage, CrossSet, Set.mem_inter_iff,
    Pfib1_Sfam, cOfF_e2f, mOfF_e2f, zero_e2f]
  constructor
  · rintro ⟨m, hm, hb⟩
    exact ⟨fun _ : Fin 1 => m, hb, hm⟩
  · rintro ⟨u, hb, hm⟩
    exact ⟨u 0, hm, hb⟩

/-! ## 4. The `Fin k ⊕ Fin 1` reindexing, for the uniform bound -/

/-- The reindexing putting the point (coordinate `0` of a tuple on `Fin (k+1)`) into the second
block of `Fin k ⊕ Fin 1`. -/
def eIdx (k : ℕ) : Fin (k + 1) → Fin k ⊕ Fin 1 :=
  Fin.cases (Sum.inr 0) (fun i : Fin k => Sum.inl i)

/-- The crossing family reindexed on `Fin k ⊕ Fin 1`, so that its last block is the point. -/
def BxP (Y : Set (Fin (k + 2) → ℝ)) (E : Set ℝ) : Set ((Fin k ⊕ Fin 1) → ℝ) :=
  (fun g : (Fin k ⊕ Fin 1) → ℝ => g ∘ eIdx k) ⁻¹' Bx Y E

@[simp] lemma elim_eIdx (c : Fin k → ℝ) (u : Fin 1 → ℝ) :
    (Sum.elim c u) ∘ eIdx k = Fin.cons (u 0) c := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j => rfl

/-- The fibre of the reindexed crossing family. -/
theorem mem_BxP_iff (Y : Set (Fin (k + 2) → ℝ)) (E : Set ℝ) (c : Fin k → ℝ) (u : Fin 1 → ℝ) :
    Sum.elim c u ∈ BxP Y E ↔ Fin.cons (u 0) c ∈ Bx Y E := by
  show (Sum.elim c u) ∘ eIdx k ∈ Bx Y E ↔ _
  rw [elim_eIdx]

end Work.WilC4
