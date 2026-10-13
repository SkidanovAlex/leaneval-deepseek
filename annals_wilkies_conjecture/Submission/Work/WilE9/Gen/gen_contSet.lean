/-
  WilE9 / `Gen` — the continuity locus of a `Gen`-graph is `Gen`.

  The construction is the negation chain of the ε-δ definition of continuity, coded with the
  `Gen` operations (complement, projection, lift, intersection with semialgebraic atoms).
  The vocabulary (the layout of the big space, the coordinate indices, the atoms `Pclose`,
  `Ptail` and the sets `Psi`, `Theta`, `T3set`, `T5set`, `Sfin`) is in
  `Submission/Work/WilE9/Gen/contDefs.lean`.

  With `close(v,δ,w) := ∀ j < n, (w j - v j)² < δ²` and

      bad(v,ε,δ,w) := w ∈ G ∧ close(v,δ,w) ∧ ε² ≤ (wₙ - vₙ)²

  the chain is

      Psi   = {bad}                      ⊆ ℝ^{(n+3)+(n+1)}
      Theta = ∃ w, Psi                   ⊆ ℝ^{n+3} = (v,ε,δ)
      T3set = ∃ δ > 0, (v,ε,δ) ∉ Theta   ⊆ ℝ^{n+2} = (v,ε)
      T5set = ∃ ε > 0, (v,ε) ∉ T3set     ⊆ ℝ^{n+1} = v
      Sfin  = G ∩ T5setᶜ

  and `v ∈ Sfin ↔ v ∈ G ∧ ∀ ε > 0, ∃ δ > 0, ∀ w ∈ G, close(v,δ,w) → |wₙ - vₙ| < ε`, which is
  the ε-δ continuity of the graph function of `G` at `v`.
-/
import Mathlib
import Submission.Work.WilE9.Defs
import Submission.Work.WilE9.Gen.contDefs
import Submission.Work.WilE9.Gen.gen_le_zero
import Submission.Work.WilE9.Gen.gen_pos_mpoly
import Submission.Work.WilE9.Gen.cont_iff_sq
import Submission.Work.WilG0.liftMN_mem
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.snocIt_natAdd

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open Classical Topology
namespace Work.WilE9.Gen
open WilkiesDesign WilkiesDesign.E

/-! ## 1. Toolkit: transport, lifts, projections, atoms -/

/-- `Gen` is invariant under the transport of a set along an equality of dimensions. -/
lemma Gen.cast_mem {F D a b : ℕ} (h : a = b) {X : Set (Fin a → ℝ)} (hX : Gen F D a X) :
    Gen F D b (h ▸ X) := by
  subst h
  exact hX

/-- Membership in the transport of a set along an equality of dimensions. -/
lemma lift_cast_mem_iff {a b : ℕ} (h : a = b) {X : Set (Fin a → ℝ)} (z : Fin b → ℝ) :
    z ∈ (h ▸ X) ↔ (fun i : Fin a => z (Fin.cast h i)) ∈ X := by
  subst h
  rfl

/-- `Fin.cast` of `Fin.addNat` is `Fin.natAdd`. -/
lemma cast_addNat_eq_natAdd (m k : ℕ) (j : Fin m) :
    Fin.cast (Nat.add_comm m k) (Fin.addNat j k) = Fin.natAdd k j := by
  ext
  simp only [Fin.val_cast, Fin.val_addNat, Fin.val_natAdd]
  exact Nat.add_comm _ _

/-- Iterating `Gen.prod_left` `k` times prepends `k` free coordinates to `X`. -/
lemma liftMN_gen {F D m : ℕ} {X : Set (Fin m → ℝ)} (h : Gen F D m X) (k : ℕ) :
    Gen (F + k) D (m + k) (Work.WilG0.liftMN k m X) := by
  induction k with
  | zero =>
    have h0 : Work.WilG0.liftMN 0 m X = X := by
      ext z
      simp only [Work.WilG0.liftMN, Set.mem_ofPred_eq]
      have hf : (fun j : Fin m => z (j.addNat 0)) = z := by
        funext j
        exact congrArg z (Fin.addNat_zero m j)
      rw [hf]
    rw [h0]
    simpa using h
  | succ k ih =>
    rw [Work.WilG0.liftMN_succ k m X]
    exact Gen.prod_left ih

/-- `X ⊆ ℝ^m` placed in the last `m` coordinates of `ℝ^{k+m}` is `Gen`. -/
lemma blkLift_gen {F D m k : ℕ} {X : Set (Fin m → ℝ)} (h : Gen F D m X) :
    Gen (F + k) D (k + m) (blkLift m k X) := by
  have h1 : Gen (F + k) D (m + k) (Work.WilG0.liftMN k m X) := liftMN_gen h k
  have h2 : Gen (F + k) D (k + m) ((Nat.add_comm m k) ▸ Work.WilG0.liftMN k m X) :=
    Gen.cast_mem (Nat.add_comm m k) h1
  have heq : (Nat.add_comm m k) ▸ Work.WilG0.liftMN k m X = blkLift m k X := by
    ext z
    rw [lift_cast_mem_iff]
    simp only [Work.WilG0.liftMN, blkLift, Set.mem_ofPred_eq]
    have hf : (fun j : Fin m => z (Fin.cast (Nat.add_comm m k) (Fin.addNat j k))) =
        (fun j : Fin m => z (Fin.natAdd k j)) := by
      funext j
      rw [cast_addNat_eq_natAdd]
    rw [hf]
  rw [heq] at h2
  exact h2

/-- Iterating the projection axiom removes `b` coordinates at the cost of `b` formats. -/
lemma projLastIter_gen (a : ℕ) : ∀ (b : ℕ) {F D : ℕ} {X : Set (Fin (a + b) → ℝ)},
    Gen F D (a + b) X → Gen (F + b) D a (Work.WilG0.projLastIter a b X) := by
  intro b
  induction b with
  | zero => intro F D X hX; simpa [Work.WilG0.projLastIter] using hX
  | succ b ih =>
    intro F D X hX
    rw [show Work.WilG0.projLastIter a (b + 1) X
        = Work.WilG0.projLastIter a b (projLast X) from rfl]
    have h1 : Gen (F + 1) D (a + b) (projLast X) := Gen.proj hX
    have hres : Gen ((F + 1) + b) D a (Work.WilG0.projLastIter a b (projLast X)) := ih h1
    exact Gen.mono (by omega) le_rfl hres

/-- Binary intersection of two `Gen`-sets of a *common* format, costing one format. -/
lemma inter₂c {F D₁ D₂ n : ℕ} {X Y : Set (Fin n → ℝ)} (hX : Gen F D₁ n X)
    (hY : Gen F D₂ n Y) : Gen (F + 1) (D₁ + D₂) n (X ∩ Y) := by
  have h := Gen.inter (fun i : Fin 2 => if i = 0 then D₁ else D₂)
    (fun i : Fin 2 => if i = 0 then X else Y) (by
      intro i
      fin_cases i
      · simpa using hX
      · simpa using hY)
  have hsum : (∑ i : Fin 2, (if i = 0 then D₁ else D₂)) = D₁ + D₂ := by
    rw [Fin.sum_univ_two]; simp
  have hset : (⋂ i : Fin 2, (if i = 0 then X else Y)) = X ∩ Y := by
    ext z
    simp [Fin.forall_fin_two]
  rw [hsum, hset] at h
  exact h

/-! ## 2. Degree bounds of the atoms -/

lemma totalDegree_X_sub_X_le {σ : Type*} (a b : σ) :
    (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial σ ℝ).totalDegree ≤ 1 := by
  calc (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial σ ℝ).totalDegree
      ≤ max (MvPolynomial.X a : MvPolynomial σ ℝ).totalDegree
          (MvPolynomial.X b).totalDegree := MvPolynomial.totalDegree_sub _ _
    _ = 1 := by simp

lemma totalDegree_Pclose_le (n : ℕ) (j : Fin n) : (Pclose n j).totalDegree ≤ 4 := by
  have h1 : ((MvPolynomial.X (iW n j) - MvPolynomial.X (iV n j) :
      MvPolynomial (Fin ((n + 3) + (n + 1))) ℝ) ^ 2).totalDegree ≤ 2 := by
    calc _ ≤ 2 * (MvPolynomial.X (iW n j) - MvPolynomial.X (iV n j) :
          MvPolynomial (Fin ((n + 3) + (n + 1))) ℝ).totalDegree :=
        MvPolynomial.totalDegree_pow _ _
      _ ≤ 2 * 1 := by
        have := totalDegree_X_sub_X_le (iW n j) (iV n j)
        omega
      _ = 2 := by norm_num
  calc (Pclose n j).totalDegree
      ≤ max ((MvPolynomial.X (iD n) ^ 2 : MvPolynomial (Fin ((n + 3) + (n + 1))) ℝ)).totalDegree
          ((MvPolynomial.X (iW n j) - MvPolynomial.X (iV n j) :
            MvPolynomial (Fin ((n + 3) + (n + 1))) ℝ) ^ 2).totalDegree := by
        rw [Pclose]; exact MvPolynomial.totalDegree_sub _ _
    _ ≤ 4 := by
        rw [MvPolynomial.totalDegree_X_pow]
        omega

lemma totalDegree_Ptail_le (n : ℕ) : (Ptail n).totalDegree ≤ 4 := by
  have h1 : ((MvPolynomial.X (iWlast n) - MvPolynomial.X (iVlast n) :
      MvPolynomial (Fin ((n + 3) + (n + 1))) ℝ) ^ 2).totalDegree ≤ 2 := by
    calc _ ≤ 2 * (MvPolynomial.X (iWlast n) - MvPolynomial.X (iVlast n) :
          MvPolynomial (Fin ((n + 3) + (n + 1))) ℝ).totalDegree :=
        MvPolynomial.totalDegree_pow _ _
      _ ≤ 2 * 1 := by
        have := totalDegree_X_sub_X_le (iWlast n) (iVlast n)
        omega
      _ = 2 := by norm_num
  calc (Ptail n).totalDegree
      ≤ max ((MvPolynomial.X (iE n) ^ 2 : MvPolynomial (Fin ((n + 3) + (n + 1))) ℝ)).totalDegree
          ((MvPolynomial.X (iWlast n) - MvPolynomial.X (iVlast n) :
            MvPolynomial (Fin ((n + 3) + (n + 1))) ℝ) ^ 2).totalDegree := by
        rw [Ptail]; exact MvPolynomial.totalDegree_sub _ _
    _ ≤ 4 := by
        rw [MvPolynomial.totalDegree_X_pow]
        omega

/-! ## 3. Reading the coordinates -/

lemma eval_Pclose (n : ℕ) (j : Fin n) (z : Fin ((n + 3) + (n + 1)) → ℝ) :
    MvPolynomial.eval z (Pclose n j)
      = (z (iD n)) ^ 2 - (z (iW n j) - z (iV n j)) ^ 2 := by
  simp [Pclose]

lemma eval_Ptail (n : ℕ) (z : Fin ((n + 3) + (n + 1)) → ℝ) :
    MvPolynomial.eval z (Ptail n)
      = (z (iE n)) ^ 2 - (z (iWlast n) - z (iVlast n)) ^ 2 := by
  simp [Ptail]

lemma snocIt_iV (n : ℕ) (x : Fin (n + 3) → ℝ) (w : Fin (n + 1) → ℝ) (j : Fin n) :
    Work.WilG0.snocIt (n + 3) (n + 1) x w (iV n j) = x (xV n j) := by
  rw [iV, xV]
  exact Work.WilG0.snocIt_castAdd (n + 3) (n + 1) x w ⟨j.val, by omega⟩

lemma snocIt_iVlast (n : ℕ) (x : Fin (n + 3) → ℝ) (w : Fin (n + 1) → ℝ) :
    Work.WilG0.snocIt (n + 3) (n + 1) x w (iVlast n) = x (xVlast n) := by
  rw [iVlast, xVlast]
  exact Work.WilG0.snocIt_castAdd (n + 3) (n + 1) x w ⟨n, by omega⟩

lemma snocIt_iE (n : ℕ) (x : Fin (n + 3) → ℝ) (w : Fin (n + 1) → ℝ) :
    Work.WilG0.snocIt (n + 3) (n + 1) x w (iE n) = x (xE n) := by
  rw [iE, xE]
  exact Work.WilG0.snocIt_castAdd (n + 3) (n + 1) x w ⟨n + 1, by omega⟩

lemma snocIt_iD (n : ℕ) (x : Fin (n + 3) → ℝ) (w : Fin (n + 1) → ℝ) :
    Work.WilG0.snocIt (n + 3) (n + 1) x w (iD n) = x (xD n) := by
  rw [iD, xD]
  exact Work.WilG0.snocIt_castAdd (n + 3) (n + 1) x w ⟨n + 2, by omega⟩

lemma snocIt_iW (n : ℕ) (x : Fin (n + 3) → ℝ) (w : Fin (n + 1) → ℝ) (j : Fin n) :
    Work.WilG0.snocIt (n + 3) (n + 1) x w (iW n j) = w (Fin.castSucc j) := by
  rw [iW]
  exact Work.WilG0.snocIt_natAdd (n + 3) (n + 1) x w ⟨j.val, by omega⟩

lemma snocIt_iWlast (n : ℕ) (x : Fin (n + 3) → ℝ) (w : Fin (n + 1) → ℝ) :
    Work.WilG0.snocIt (n + 3) (n + 1) x w (iWlast n) = w (Fin.last n) := by
  rw [iWlast]
  exact Work.WilG0.snocIt_natAdd (n + 3) (n + 1) x w (Fin.last n)

lemma snocIt_natAdd_fun (n : ℕ) (x : Fin (n + 3) → ℝ) (w : Fin (n + 1) → ℝ) :
    (fun i : Fin (n + 1) => Work.WilG0.snocIt (n + 3) (n + 1) x w (Fin.natAdd (n + 3) i))
      = w := by
  funext i
  exact Work.WilG0.snocIt_natAdd (n + 3) (n + 1) x w i

lemma snoc_xV (n : ℕ) (q : Fin (n + 2) → ℝ) (d : ℝ) (j : Fin n) :
    (Fin.snoc q d : Fin (n + 3) → ℝ) (xV n j) = q (qV n j) := by
  rw [xV, qV]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) d q ⟨j.val, by omega⟩

lemma snoc_xVlast (n : ℕ) (q : Fin (n + 2) → ℝ) (d : ℝ) :
    (Fin.snoc q d : Fin (n + 3) → ℝ) (xVlast n) = q (qVlast n) := by
  rw [xVlast, qVlast]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) d q ⟨n, by omega⟩

lemma snoc_xE (n : ℕ) (q : Fin (n + 2) → ℝ) (d : ℝ) :
    (Fin.snoc q d : Fin (n + 3) → ℝ) (xE n) = q (qE n) := by
  rw [xE, qE]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) d q ⟨n + 1, by omega⟩

lemma snoc_xD (n : ℕ) (q : Fin (n + 2) → ℝ) (d : ℝ) :
    (Fin.snoc q d : Fin (n + 3) → ℝ) (xD n) = d := by
  rw [xD]
  exact Fin.snoc_last (α := fun _ => ℝ) d q

lemma snoc_xD_lit (n : ℕ) (q : Fin (n + 2) → ℝ) (d : ℝ) :
    (Fin.snoc q d : Fin (n + 3) → ℝ) (Fin.last (n + 2)) = d :=
  Fin.snoc_last (α := fun _ => ℝ) d q

lemma snoc_qV (n : ℕ) (v : Fin (n + 1) → ℝ) (e : ℝ) (j : Fin n) :
    (Fin.snoc v e : Fin (n + 2) → ℝ) (qV n j) = v (vV n j) := by
  rw [qV, vV]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) e v (Fin.castSucc j)

lemma snoc_qVlast (n : ℕ) (v : Fin (n + 1) → ℝ) (e : ℝ) :
    (Fin.snoc v e : Fin (n + 2) → ℝ) (qVlast n) = v (Fin.last n) := by
  rw [qVlast]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) e v (Fin.last n)

lemma snoc_qE (n : ℕ) (v : Fin (n + 1) → ℝ) (e : ℝ) :
    (Fin.snoc v e : Fin (n + 2) → ℝ) (qE n) = e := by
  rw [qE]
  exact Fin.snoc_last (α := fun _ => ℝ) e v

lemma snoc_qE_lit (n : ℕ) (v : Fin (n + 1) → ℝ) (e : ℝ) :
    (Fin.snoc v e : Fin (n + 2) → ℝ) (Fin.last (n + 1)) = e :=
  Fin.snoc_last (α := fun _ => ℝ) e v

/-! ## 4. Membership in the sets of the chain -/

lemma mem_Psi {n : ℕ} {G : Set (Fin (n + 1) → ℝ)} {z : Fin ((n + 3) + (n + 1)) → ℝ} :
    z ∈ Psi n G ↔
      (fun i : Fin (n + 1) => z (Fin.natAdd (n + 3) i)) ∈ G ∧
      (∀ j : Fin n, (z (iW n j) - z (iV n j)) ^ 2 < (z (iD n)) ^ 2) ∧
      (z (iE n)) ^ 2 ≤ (z (iWlast n) - z (iVlast n)) ^ 2 := by
  simp only [Psi, blkLift, closeAtom, tailAtom, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_ofPred_eq, eval_Pclose, eval_Ptail, sub_pos, sub_nonpos]
  tauto

lemma mem_Theta {n : ℕ} {G : Set (Fin (n + 1) → ℝ)} {x : Fin (n + 3) → ℝ} :
    x ∈ Theta n G ↔ ∃ w : Fin (n + 1) → ℝ,
      w ∈ G ∧ (∀ j : Fin n, (w (Fin.castSucc j) - x (xV n j)) ^ 2 < (x (xD n)) ^ 2) ∧
      (x (xE n)) ^ 2 ≤ (w (Fin.last n) - x (xVlast n)) ^ 2 := by
  rw [Theta, Work.WilG0.projLastIter_eq]
  simp only [mem_Psi, snocIt_natAdd_fun, snocIt_iV, snocIt_iW, snocIt_iE, snocIt_iD,
    snocIt_iVlast, snocIt_iWlast, Set.mem_ofPred_eq]

lemma mem_T3set {n : ℕ} {G : Set (Fin (n + 1) → ℝ)} {q : Fin (n + 2) → ℝ} :
    q ∈ T3set n G ↔ ∃ δ : ℝ, 0 < δ ∧ ¬ ∃ w : Fin (n + 1) → ℝ, w ∈ G ∧
      (∀ j : Fin n, (w (Fin.castSucc j) - q (qV n j)) ^ 2 < δ ^ 2) ∧
      (q (qE n)) ^ 2 ≤ (w (Fin.last n) - q (qVlast n)) ^ 2 := by
  simp only [T3set, projLast, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff,
    mem_Theta, snoc_xV, snoc_xVlast, snoc_xE, snoc_xD, snoc_xD_lit]

lemma mem_T5set {n : ℕ} {G : Set (Fin (n + 1) → ℝ)} {v : Fin (n + 1) → ℝ} :
    v ∈ T5set n G ↔ ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
      ∃ w : Fin (n + 1) → ℝ, w ∈ G ∧
        (∀ j : Fin n, (w (Fin.castSucc j) - v (vV n j)) ^ 2 < δ ^ 2) ∧
        ε ^ 2 ≤ (w (Fin.last n) - v (Fin.last n)) ^ 2 := by
  simp only [T5set, projLast, mem_T3set, Set.mem_ofPred_eq, Set.mem_inter_iff,
    Set.mem_compl_iff, snoc_qV, snoc_qVlast, snoc_qE, snoc_qE_lit]
  constructor
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε, hε, fun δ hδ => ?_⟩
    by_contra hc
    exact h ⟨δ, hδ, hc⟩
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε, hε, ?_⟩
    rintro ⟨δ, hδ, hc⟩
    exact hc (h δ hδ)

lemma mem_Sfin {n : ℕ} {G : Set (Fin (n + 1) → ℝ)} {v : Fin (n + 1) → ℝ} :
    v ∈ Sfin n G ↔ v ∈ G ∧ ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
      ∃ w : Fin (n + 1) → ℝ, w ∈ G ∧
        (∀ j : Fin n, (w (Fin.castSucc j) - v (vV n j)) ^ 2 < δ ^ 2) ∧
        ε ^ 2 ≤ (w (Fin.last n) - v (Fin.last n)) ^ 2 := by
  simp only [Sfin, Set.mem_inter_iff, Set.mem_compl_iff, mem_T5set]

/-- **The key equivalence.**  `Sfin n G` is the continuity locus, in the squared sup-metric form
of `Work.WilE9.Gen.cont_iff_sq`. -/
lemma Sfin_iff {n : ℕ} (G : Set (Fin (n + 1) → ℝ)) (v : Fin (n + 1) → ℝ) :
    v ∈ Sfin n G ↔ v ∈ G ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ w : Fin (n + 1) → ℝ,
      w ∈ G → (∀ j : Fin n, (w (Fin.castSucc j) - v (vV n j)) ^ 2 < δ ^ 2) →
      (w (Fin.last n) - v (Fin.last n)) ^ 2 < ε ^ 2 := by
  rw [mem_Sfin]
  constructor
  · rintro ⟨hG, h⟩
    push_neg at h
    exact ⟨hG, h⟩
  · rintro ⟨hG, h⟩
    refine ⟨hG, ?_⟩
    rintro ⟨ε, hε, hbad⟩
    obtain ⟨δ, hδ, hw⟩ := h ε hε
    obtain ⟨w, hwG, hcl, hle⟩ := hbad δ hδ
    exact absurd (hw w hwG hcl) (not_lt.mpr hle)

/-! ## 5. The `Gen`-chain -/

/-- The `Gen`-membership of the continuity locus, with constant format and linear degree
budgets. -/
lemma Sfin_gen {F D n : ℕ} {G : Set (Fin (n + 1) → ℝ)} (hG : Gen F D (n + 1) G) :
    Gen (F + 3 * n + 25) (2 * D + 6 * n + 30) (n + 1) (Sfin n G) := by
  have hClose : Gen (((n + 3) + (n + 1)) + 3 + 1) (6 * n) ((n + 3) + (n + 1))
      (⋂ j : Fin n, closeAtom n j) := by
    have h := Gen.inter (fun _ : Fin n => 6) (fun j : Fin n => closeAtom n j)
      (fun j => Gen.monoD (by have := totalDegree_Pclose_le n j; omega)
        (gen_pos_mpoly (Pclose n j)))
    have hsum : (∑ _ : Fin n, (6 : ℕ)) = 6 * n := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
    rwa [hsum] at h
  have hTail : Gen (((n + 3) + (n + 1)) + 2) 6 ((n + 3) + (n + 1)) (tailAtom n) := by
    have h := gen_le_zero (Ptail n)
    exact Gen.monoD (by have := totalDegree_Ptail_le n; omega) h
  have hatomD : Gen (n + 6) 3 (n + 3) {z : Fin (n + 3) → ℝ | 0 < z (xD n)} := by
    simpa using gen_pos_mpoly (MvPolynomial.X (xD n) : MvPolynomial (Fin (n + 3)) ℝ)
  have hatomE : Gen (n + 5) 3 (n + 2) {z : Fin (n + 2) → ℝ | 0 < z (qE n)} := by
    simpa using gen_pos_mpoly (MvPolynomial.X (qE n) : MvPolynomial (Fin (n + 2)) ℝ)
  have hPsi : Gen (F + 2 * n + 10) (D + 6 * n + 6) ((n + 3) + (n + 1)) (Psi n G) := by
    have hA1 : Gen (F + 2 * n + 8) D ((n + 3) + (n + 1)) (blkLift (n + 1) (n + 3) G) :=
      Gen.mono (by omega) le_rfl (blkLift_gen hG)
    have hA2 : Gen (F + 2 * n + 8) (6 * n) ((n + 3) + (n + 1))
        (⋂ j : Fin n, closeAtom n j) := Gen.mono (by omega) le_rfl hClose
    have hA3 : Gen (F + 2 * n + 8) 6 ((n + 3) + (n + 1)) (tailAtom n) :=
      Gen.mono (by omega) le_rfl hTail
    have hi1 := inter₂c hA1 hA2
    have hA3' : Gen (F + 2 * n + 8 + 1) 6 ((n + 3) + (n + 1)) (tailAtom n) :=
      Gen.mono (by omega) le_rfl hA3
    have hi2 := inter₂c hi1 hA3'
    exact Gen.mono (by omega) le_rfl hi2
  have hTheta : Gen (F + 3 * n + 11) (D + 6 * n + 6) (n + 3) (Theta n G) :=
    Gen.mono (by omega) le_rfl (projLastIter_gen (n + 3) (n + 1) hPsi)
  have hT3 : Gen (F + 3 * n + 14) (D + 6 * n + 9) (n + 2) (T3set n G) := by
    have hc : Gen (F + 3 * n + 12) (D + 6 * n + 6) (n + 3) (Theta n G)ᶜ :=
      Gen.compl (Gen.mono (by omega) le_rfl hTheta)
    have ha : Gen (F + 3 * n + 12) 3 (n + 3) {z : Fin (n + 3) → ℝ | 0 < z (xD n)} :=
      Gen.mono (by omega) le_rfl hatomD
    exact Gen.mono (by omega) (by omega) (Gen.proj (inter₂c ha hc))
  have hT5 : Gen (F + 3 * n + 17) (D + 6 * n + 12) (n + 1) (T5set n G) := by
    have hc : Gen (F + 3 * n + 15) (D + 6 * n + 9) (n + 2) (T3set n G)ᶜ :=
      Gen.compl (Gen.mono (by omega) le_rfl hT3)
    have ha : Gen (F + 3 * n + 15) 3 (n + 2) {z : Fin (n + 2) → ℝ | 0 < z (qE n)} :=
      Gen.mono (by omega) le_rfl hatomE
    exact Gen.mono (by omega) (by omega) (Gen.proj (inter₂c ha hc))
  have hc : Gen (F + 3 * n + 18) (D + 6 * n + 12) (n + 1) (T5set n G)ᶜ :=
    Gen.compl (Gen.mono (by omega) le_rfl hT5)
  have hG' : Gen (F + 3 * n + 18) D (n + 1) G := Gen.mono (by omega) le_rfl hG
  exact Gen.mono (by omega) (by omega) (inter₂c hG' hc)

/-! ## 6. The theorem -/

/-- **The continuity locus of a `Gen`-graph is `Gen`.**  If `G ⊆ ℝⁿ⁺¹` is a `Gen`-set (thought
of as the graph of a function `f`), then the set of points `v ∈ G` at which `f` is continuous at
`Fin.init v` is again `Gen`, with constant format budget and polynomial degree budget.  This is
the continuity half of the `C^k` characterisation
(`Work.WilE9.Deriv.contDiffAt_iff_partials`) and is needed to characterise
`interior {x | ContDiffAt ℝ k f x}`.  The sup-metric (`|x' j - Fin.init v j| < δ`) is used for
the same reason as in `gen_diffSet`: its balls are a neighbourhood basis and its atoms are
semialgebraic. -/
theorem gen_contSet (F n : ℕ) : ∃ (a : ℕ) (b : Polynomial ℕ),
    ∀ (D : ℕ) (G : Set (Fin (n + 1) → ℝ)),
      WilkiesDesign.E.Gen F D (n + 1) G → WilkiesDesign.E.Gen a (b.eval D) (n + 1)
        {v : Fin (n + 1) → ℝ | v ∈ G ∧
          ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' : Fin n → ℝ,
            (∀ j : Fin n, |x' j - Fin.init v j| < δ) →
            ∀ v' : ℝ, Fin.snoc x' v' ∈ G → |v' - v (Fin.last n)| < ε} := by
  refine ⟨F + 3 * n + 25, Polynomial.C (6 * n + 30) + Polynomial.C 2 * Polynomial.X, ?_⟩
  intro D G hG
  have hgen : Gen (F + 3 * n + 25) (2 * D + 6 * n + 30) (n + 1) (Sfin n G) := Sfin_gen hG
  have hb : (Polynomial.C (6 * n + 30) + Polynomial.C 2 * Polynomial.X).eval D
      = 2 * D + 6 * n + 30 := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  rw [hb]
  have hset : {v : Fin (n + 1) → ℝ | v ∈ G ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' : Fin n → ℝ,
          (∀ j : Fin n, |x' j - Fin.init v j| < δ) →
          ∀ v' : ℝ, Fin.snoc x' v' ∈ G → |v' - v (Fin.last n)| < ε} = Sfin n G := by
    ext v
    rw [Sfin_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (cont_iff_sq G v).mp h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1, (cont_iff_sq G v).mpr h2⟩⟩
  rw [hset]
  exact hgen

end Work.WilE9.Gen
