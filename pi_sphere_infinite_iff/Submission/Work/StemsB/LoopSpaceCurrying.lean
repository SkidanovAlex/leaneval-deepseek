import Mathlib

/-!
# Currying an `(n+1)`-cube into an `n`-cube of loops

For a topological space `X` with base point `x`, the space of `(n+1)`-dimensional generalized
loops `Ω^(n+1) X x` is the space of `n`-dimensional generalized loops in the loop space
`Ω X x = Path x x`.  This file constructs the underlying *homeomorphism of generalized loop
spaces* `Faux : Ω^(n+1) X x → Ω^n (Path x x) (Path.refl x)`, its inverse `Gaux`, and shows that
it identifies the homotopy-relative-to-boundary relations and the `GenLoop.transAt`
concatenations.  It is the geometric input for `Work.StemsB.homotopyGroup_loopSpace`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.StemsB

section
variable {X : Type*} [TopologicalSpace X] {x : X}

/-- `(s, t) ↦ Fin.cons s t` is continuous. -/
private lemma cont_cons (n : ℕ) :
    Continuous (fun p : unitInterval × (Fin n → unitInterval) =>
      (Fin.cons p.1 p.2 : Fin (n+1) → unitInterval)) := by
  apply continuous_pi
  intro j
  cases j using Fin.cases with
  | zero => simpa using continuous_fst
  | succ i =>
    change Continuous (fun a : unitInterval × (Fin n → unitInterval) =>
      (fun f : Fin n → unitInterval => f i) (Prod.snd a))
    exact (continuous_apply i).comp continuous_snd

/-- Splitting off the first coordinate: an `(n+1)`-cube of `X` gives an `n`-cube of paths. -/
def Faux (n : ℕ) (p : GenLoop (Fin (n+1)) X x) : GenLoop (Fin n) (Path x x) (Path.refl x) :=
  ⟨⟨fun t => ⟨⟨fun s => p (Fin.cons s t), by
        exact (map_continuous p).comp ((cont_cons n).comp (continuous_id.prodMk continuous_const))⟩,
      by
        show p (Fin.cons (0:unitInterval) t) = x
        exact p.2 _ ⟨0, Or.inl (by simp)⟩,
      by
        show p (Fin.cons (1:unitInterval) t) = x
        exact p.2 _ ⟨0, Or.inr (by simp)⟩⟩,
    by
      apply Path.continuous_uncurry_iff.mp
      have h : Continuous fun q : (Fin n → unitInterval) × unitInterval => p (Fin.cons q.2 q.1) :=
        (map_continuous p).comp ((cont_cons n).comp (continuous_snd.prodMk continuous_fst))
      exact h⟩,
    by
      intro t ht
      apply Path.ext
      funext s
      show p (Fin.cons s t) = x
      obtain ⟨i, hi | hi⟩ := ht
      · exact p.2 _ ⟨i.succ, by simp [hi]⟩
      · exact p.2 _ ⟨i.succ, by simp [hi]⟩⟩

@[simp] theorem Faux_apply (n : ℕ) (p : GenLoop (Fin (n+1)) X x) (t : Fin n → unitInterval)
    (s : unitInterval) : (Faux n p t) s = p (Fin.cons s t) := rfl

theorem Faux_apply' (n : ℕ) (p : GenLoop (Fin (n+1)) X x) (t : Fin n → unitInterval)
    (s : unitInterval) : ((Faux n p).1 t) s = p.1 (Fin.cons s t) := rfl

/-- Reassembling: an `n`-cube of paths gives an `(n+1)`-cube of `X`. -/
def Gaux (n : ℕ) (q : GenLoop (Fin n) (Path x x) (Path.refl x)) : GenLoop (Fin (n+1)) X x :=
  ⟨⟨fun v => (q (Fin.tail v)) (v 0), by
      have htail : Continuous fun v : (Fin (n+1) → unitInterval) => Fin.tail v := by
        apply continuous_pi
        intro i
        change Continuous (fun v : Fin (n+1) → unitInterval => v i.succ)
        exact continuous_apply i.succ
      exact ((map_continuous q).comp htail).eval (continuous_apply 0)⟩,
    by
      intro v hv
      show (q (Fin.tail v)) (v 0) = x
      obtain ⟨i, hi⟩ := hv
      rcases hi with hi | hi
      · cases i using Fin.cases with
        | zero =>
          rw [hi]
          exact Path.source (q (Fin.tail v))
        | succ j =>
          have h : q (Fin.tail v) = Path.refl x :=
            q.2 _ ⟨j, Or.inl (by simpa [Fin.tail] using hi)⟩
          rw [h]
          exact Path.refl_apply x (v 0)
      · cases i using Fin.cases with
        | zero =>
          rw [hi]
          exact Path.target (q (Fin.tail v))
        | succ j =>
          have h : q (Fin.tail v) = Path.refl x :=
            q.2 _ ⟨j, Or.inr (by simpa [Fin.tail] using hi)⟩
          rw [h]
          exact Path.refl_apply x (v 0)⟩

@[simp] theorem Gaux_apply (n : ℕ) (q : GenLoop (Fin n) (Path x x) (Path.refl x))
    (v : Fin (n+1) → unitInterval) : Gaux n q v = (q (Fin.tail v)) (v 0) := rfl

theorem Gaux_Faux (n : ℕ) (p : GenLoop (Fin (n+1)) X x) : Gaux n (Faux n p) = p := by
  apply GenLoop.ext
  intro v
  simp only [Gaux_apply, Faux_apply, Fin.cons_self_tail]

theorem Faux_Gaux (n : ℕ) (q : GenLoop (Fin n) (Path x x) (Path.refl x)) :
    Faux n (Gaux n q) = q := by
  apply GenLoop.ext
  intro t
  apply Path.ext
  funext s
  simp only [Faux_apply, Gaux_apply, Fin.tail_cons, Fin.cons_zero]

theorem Faux_homotopic (n : ℕ) {p q : GenLoop (Fin (n+1)) X x} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (Faux n p) (Faux n q) := by
  rcases h with ⟨K⟩
  refine ⟨⟨⟨⟨fun w => ⟨⟨fun s => K (w.1, Fin.cons s w.2), ?_⟩, ?_, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩⟩
  case _ =>
    exact K.continuous.comp ((continuous_const : Continuous fun _ : unitInterval => w.1).prodMk
      ((cont_cons n).comp (continuous_id.prodMk (continuous_const : Continuous fun _ : unitInterval => w.2))))
  case _ =>
    show K (w.1, Fin.cons (0:unitInterval) w.2) = x
    exact (K.eq_fst w.1 ⟨0, Or.inl (by simp)⟩).trans (p.2 _ ⟨0, Or.inl (by simp)⟩)
  case _ =>
    show K (w.1, Fin.cons (1:unitInterval) w.2) = x
    exact (K.eq_fst w.1 ⟨0, Or.inr (by simp)⟩).trans (p.2 _ ⟨0, Or.inr (by simp)⟩)
  case _ =>
    apply Path.continuous_uncurry_iff.mp
    change Continuous fun y : (I × (Fin n → I)) × I => K (y.1.1, (Fin.cons y.2 y.1.2 : Fin (n+1) → I))
    exact K.continuous.comp ((continuous_fst.fst).prodMk
      ((cont_cons n).comp (continuous_snd.prodMk (continuous_fst.snd))))
  case _ =>
    intro t
    apply Path.ext
    funext s
    show K (0, Fin.cons s t) = p (Fin.cons s t)
    rw [K.apply_zero]
    rfl
  case _ =>
    intro t
    apply Path.ext
    funext s
    show K (1, Fin.cons s t) = q (Fin.cons s t)
    rw [K.apply_one]
    rfl
  case _ =>
    intro τ t ht
    apply Path.ext
    funext s
    show K (τ, Fin.cons s t) = p (Fin.cons s t)
    obtain ⟨i, hi | hi⟩ := ht
    · exact K.eq_fst τ ⟨i.succ, Or.inl (by simpa using hi)⟩
    · exact K.eq_fst τ ⟨i.succ, Or.inr (by simpa using hi)⟩

theorem Gaux_homotopic (n : ℕ) {p q : GenLoop (Fin (n+1)) X x}
    (h : GenLoop.Homotopic (Faux n p) (Faux n q)) : GenLoop.Homotopic p q := by
  rcases h with ⟨K⟩
  refine ⟨⟨⟨⟨fun w => (K (w.1, Fin.tail w.2)) (w.2 0), ?_⟩, ?_, ?_⟩, ?_⟩⟩
  case _ =>
    have htail : Continuous fun w : I × (Fin (n+1) → I) => Fin.tail w.2 := by
      apply continuous_pi
      intro i
      change Continuous (fun w : I × (Fin (n+1) → I) => w.2 i.succ)
      exact (continuous_apply i.succ).comp continuous_snd
    exact ((K.continuous.comp (continuous_fst.prodMk htail)).eval
      ((continuous_apply 0).comp continuous_snd))
  case _ =>
    intro v
    change (K (0, Fin.tail v)) (v 0) = p.1 v
    rw [K.apply_zero, Faux_apply', Fin.cons_self_tail]
  case _ =>
    intro v
    change (K (1, Fin.tail v)) (v 0) = q.1 v
    rw [K.apply_one, Faux_apply', Fin.cons_self_tail]
  case _ =>
    intro τ v hv
    change (K (τ, Fin.tail v)) (v 0) = p.1 v
    obtain ⟨i, hi⟩ := hv
    rcases hi with hi | hi
    · cases i using Fin.cases with
      | zero =>
        rw [hi, Path.source]
        exact (p.2 v ⟨0, Or.inl hi⟩).symm
      | succ j =>
        have hbd : Fin.tail v ∈ Cube.boundary (Fin n) := ⟨j, Or.inl (by simpa [Fin.tail] using hi)⟩
        rw [K.eq_fst τ hbd, Faux_apply', Fin.cons_self_tail]
    · cases i using Fin.cases with
      | zero =>
        rw [hi, Path.target]
        exact (p.2 v ⟨0, Or.inr hi⟩).symm
      | succ j =>
        have hbd : Fin.tail v ∈ Cube.boundary (Fin n) := ⟨j, Or.inr (by simpa [Fin.tail] using hi)⟩
        rw [K.eq_fst τ hbd, Faux_apply', Fin.cons_self_tail]

theorem path_ite_apply {c : Prop} [Decidable c] (A B : Path x x) (s : unitInterval) :
    ((if c then A else B : Path x x)) s = if c then A s else B s := by
  by_cases h : c <;> simp [h]

theorem Faux_transAt (k : ℕ) (p q : GenLoop (Fin (k+2)) X x) :
    Faux (k+1) (GenLoop.transAt (Fin.succ (0 : Fin (k+1))) q p) =
      GenLoop.transAt (0 : Fin (k+1)) (Faux (k+1) q) (Faux (k+1) p) := by
  apply GenLoop.ext
  intro t
  apply Path.ext
  funext s
  rw [Faux_apply]
  simp only [GenLoop.transAt, GenLoop.coe_copy, path_ite_apply, Faux_apply, Fin.cons_succ]
  simp only [← Fin.cons_update]

/-- The underlying bijection `Ω^(n+1) X x ≃ Ω^n (Path x x) (Path.refl x)`. -/
def stepEquiv (n : ℕ) : GenLoop (Fin (n+1)) X x ≃ GenLoop (Fin n) (Path x x) (Path.refl x) where
  toFun := Faux n
  invFun := Gaux n
  left_inv := Gaux_Faux n
  right_inv := Faux_Gaux n

/-- The induced bijection of homotopy groups. -/
noncomputable def stepEquivGroup (n : ℕ) :
    HomotopyGroup (Fin (n+1)) X x ≃ HomotopyGroup (Fin n) (Path x x) (Path.refl x) :=
  Quotient.congr (stepEquiv n) (fun _ _ => ⟨Faux_homotopic n, Gaux_homotopic n⟩)

theorem stepEquivGroup_mk (n : ℕ) (p : GenLoop (Fin (n+1)) X x) :
    stepEquivGroup n ⟦p⟧ = ⟦Faux n p⟧ := rfl

end

end Work.StemsB
