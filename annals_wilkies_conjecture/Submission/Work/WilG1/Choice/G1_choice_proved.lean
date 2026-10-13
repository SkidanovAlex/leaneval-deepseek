/-
  WilG1/Choice/G1_choice_proved — effective definable choice in `n` coordinates, i.e. the
  statement `G1_choice` of `Submission/Work/Wilkies/CG/Spec.lean`.

  `oneDim_choice` (the `n = 1` case) selects the last coordinate of an `Ω`-set `X ⊆ ℝ^{p+1}`
  as a function of the first `p`.  Iterating it `n` times produces a section
  `f : ℝ^p → ℝ^n` of `X ⊆ ℝ^{p+n}`: given `g` selecting the last coordinate, the set
  `Z = {w | Fin.snoc w (g w) ∈ X}` is the projection of `X ∩ graphOf g`, whence the induction
  hypothesis produces `h : ℝ^p → ℝ^n` whose graph selects inside `Z`, and the section is
  `l ↦ Fin.snoc (h l) (g (Fin.append l (h l)))`.

  All `Ω`-bounds are combined as polynomials in the single degree parameter `D`:
  `Z` gets degree `(X + b₁).eval D`, whence the graph of `h` gets `(b₂.comp (X + b₁)).eval D`,
  and the final degree polynomial is `b₂.comp (X + b₁) + b₁`; the final format is
  `max (a₂ + 1) a₁ + 1`.
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG5.Basic
import Submission.Work.WilG1.Choice.G1Sel.OneDimG1

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG1.Choice

open WilkiesDesign WilkiesConjecture

/-! ## 0. The graph of a section `ℝ^p → ℝ^n` -/

/-- The graph of `f : ℝ^p → ℝ^n` inside `ℝ^{p+n}` (parameters first, values last). -/
def gset {p n : ℕ} (f : (Fin p → ℝ) → (Fin n → ℝ)) : Set (Fin (p + n) → ℝ) :=
  {z | ∀ j : Fin n, z (Fin.natAdd p j) = f (fun i => z (Fin.castAdd n i)) j}

@[simp] theorem mem_gset {p n : ℕ} {f : (Fin p → ℝ) → (Fin n → ℝ)} {z : Fin (p + n) → ℝ} :
    z ∈ gset f ↔ ∀ j : Fin n, z (Fin.natAdd p j) = f (fun i => z (Fin.castAdd n i)) j :=
  Iff.rfl

/-! ## 1. Index lemmas -/

theorem init_natAdd {p n : ℕ} (z : Fin (p + (n + 1)) → ℝ) (j : Fin n) :
    (Fin.init z) (Fin.natAdd p j) = z (Fin.natAdd p (Fin.castSucc j)) := by
  have h : Fin.castSucc (Fin.natAdd p j) = Fin.natAdd p (Fin.castSucc j) := Fin.ext rfl
  show z (Fin.castSucc (Fin.natAdd p j)) = z (Fin.natAdd p (Fin.castSucc j))
  rw [h]

theorem init_castAdd {p n : ℕ} (z : Fin (p + (n + 1)) → ℝ) (i : Fin p) :
    (Fin.init z) (Fin.castAdd n i) = z (Fin.castAdd (n + 1) i) := by
  have h : Fin.castSucc (Fin.castAdd n i) = Fin.castAdd (n + 1) i := Fin.ext rfl
  show z (Fin.castSucc (Fin.castAdd n i)) = z (Fin.castAdd (n + 1) i)
  rw [h]

theorem castSucc_natAdd_eq {p n : ℕ} (j : Fin n) :
    (Fin.castSucc (Fin.natAdd p j) : Fin (p + n + 1)) = Fin.natAdd p (Fin.castSucc j) :=
  Fin.ext rfl

theorem natAdd_last_eq {p n : ℕ} : Fin.natAdd p (Fin.last n) = Fin.last (p + n) :=
  Fin.ext rfl

/-- Reconstruction of a tuple from its first `p` and last `n` coordinates. -/
theorem eq_append_of {p n : ℕ} {w : Fin (p + n) → ℝ} {l : Fin p → ℝ} {u : Fin n → ℝ}
    (h1 : ∀ i : Fin p, w (Fin.castAdd n i) = l i)
    (h2 : ∀ j : Fin n, w (Fin.natAdd p j) = u j) : w = Fin.append l u := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    rw [h1 i, Fin.append_left]
  · intro j
    rw [h2 j, Fin.append_right]

/-- **The iteration step.**  Given a section `h` of `Z = {w | Fin.snoc w (g w) ∈ X}`, the
composite `l ↦ Fin.snoc (h l) (g (Fin.append l (h l)))` is a section of `X`, and its graph is
the intersection of the lifted graph of `h` with the graph of `g`. -/
theorem gset_snoc_iff {p n : ℕ} (h : (Fin p → ℝ) → (Fin n → ℝ))
    (g : (Fin (p + n) → ℝ) → ℝ) (z : Fin (p + (n + 1)) → ℝ) :
    z ∈ gset (fun l : Fin p → ℝ => Fin.snoc (h l) (g (Fin.append l (h l)))) ↔
      Fin.init z ∈ gset h ∧ z (Fin.last (p + n)) = g (Fin.init z) := by
  have hAB : (fun i : Fin p => z (Fin.castAdd (n + 1) i)) =
      (fun i : Fin p => (Fin.init z) (Fin.castAdd n i)) := by
    funext i
    exact (init_castAdd z i).symm
  have hinit : Fin.init z ∈ gset h →
      Fin.init z = Fin.append (fun i : Fin p => z (Fin.castAdd (n + 1) i))
        (h (fun i : Fin p => z (Fin.castAdd (n + 1) i))) := by
    intro hzH
    refine eq_append_of (w := Fin.init z) ?_ ?_
    · intro i
      exact (init_castAdd z i).symm
    · intro j
      have hj := hzH j
      rw [← hAB] at hj
      exact hj
  constructor
  · intro hz
    have hzH : Fin.init z ∈ gset h := by
      intro j
      have hj := hz (Fin.castSucc j)
      simp only [Fin.snoc_castSucc] at hj
      rw [init_natAdd z j]
      rw [hj, hAB]
    refine ⟨hzH, ?_⟩
    have hj := hz (Fin.last n)
    simp only [Fin.snoc_last] at hj
    rw [natAdd_last_eq] at hj
    rw [hj, hinit hzH]
  · rintro ⟨hzH, hzlast⟩
    intro j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc]
      rw [← castSucc_natAdd_eq]
      change (Fin.init z) (Fin.natAdd p j') = h (fun i => z (Fin.castAdd (n + 1) i)) j'
      rw [hinit hzH, Fin.append_right]
    · simp only [Fin.snoc_last]
      rw [natAdd_last_eq, hzlast, hinit hzH]

/-! ## 2. Small `Ω`-calculus helpers (kept local so that this module's dependency set is
small) -/

theorem pair_mem {S : SOMin} {n F₁ F₂ D₁ D₂ : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : A ∈ S.Ω F₁ D₁ n) (hB : B ∈ S.Ω F₂ D₂ n) :
    A ∩ B ∈ S.Ω (max F₁ F₂ + 1) (D₁ + D₂) n := by
  have h1 : A ∈ S.Ω (max F₁ F₂) D₁ n := Omega.mono hA (le_max_left F₁ F₂) le_rfl
  have h2 : B ∈ S.Ω (max F₁ F₂) D₂ n := Omega.mono hB (le_max_right F₁ F₂) le_rfl
  have h := S.inter (fun i : Fin 2 => if i = 0 then D₁ else D₂)
    (fun i : Fin 2 => if i = 0 then A else B)
    (by intro i
        fin_cases i
        · simpa using h1
        · simpa using h2)
  rw [Omega.iInter_fin_two] at h
  have hs : (∑ i : Fin 2, (if i = 0 then D₁ else D₂)) = D₁ + D₂ := by
    rw [Fin.sum_univ_two]; simp
  rw [hs] at h
  exact h

/-- The projection of `X ∩ graphOf g` is the region on which `g` selects inside `X`. -/
theorem projLast_inter_graphOf {p : ℕ} (X : Set (Fin (p + 1) → ℝ))
    (g : (Fin p → ℝ) → ℝ) :
    projLast (X ∩ WilkiesDesign.graphOf g) = {w : Fin p → ℝ | Fin.snoc w (g w) ∈ X} := by
  ext w
  simp only [projLast, Set.mem_ofPred_eq, Set.mem_inter_iff, WilkiesDesign.graphOf,
    Fin.init_snoc, Fin.snoc_last]
  constructor
  · rintro ⟨t, htX, htg⟩
    rwa [htg] at htX
  · intro hw
    exact ⟨g w, hw, rfl⟩

/-- Membership in the graph of a function of one variable. -/
theorem mem_graphOf {n : ℕ} (g : (Fin n → ℝ) → ℝ) (z : Fin (n + 1) → ℝ) :
    z ∈ WilkiesDesign.graphOf g ↔ z (Fin.last n) = g (Fin.init z) := Iff.rfl

/-! ## 3. The main induction -/

theorem gset_aux (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) :
    ∀ (n F p : ℕ), ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) (X : Set (Fin (p + n) → ℝ)), X ∈ S.Ω F D (p + n) →
        ∃ f : (Fin p → ℝ) → (Fin n → ℝ),
          (∀ l : Fin p → ℝ, (∃ y, Fin.append l y ∈ X) → Fin.append l (f l) ∈ X) ∧
          gset f ∈ S.Ω a (b.eval D) (p + n) := by
  intro n
  induction n with
  | zero =>
    intro F p
    refine ⟨p + 4, Polynomial.C 4, ?_⟩
    intro D X hX
    refine ⟨fun _ : Fin p → ℝ => Fin.elim0, ?_, ?_⟩
    · intro l hy
      obtain ⟨y, hyX⟩ := hy
      have hy0 : y = Fin.elim0 := by funext i; exact i.elim0
      rw [hy0] at hyX
      exact hyX
    · have hset : gset (fun _ : Fin p → ℝ => (Fin.elim0 : Fin 0 → ℝ)) = Set.univ := by
        ext z
        simp only [mem_gset, Set.mem_univ, iff_true]
        intro j
        exact j.elim0
      rw [hset]
      have h := Work.WilG5.univ_mem (S := S) (n := p + 0)
      simpa [Polynomial.eval_C] using h
  | succ n ih =>
    intro F p
    obtain ⟨a₁, b₁, h₁⟩ := G1Sel.oneDimG1 (S := S) hcd F (p + n)
    obtain ⟨a₂, b₂, h₂⟩ := ih (max F a₁ + 2) p
    refine ⟨max (a₂ + 1) a₁ + 1, (b₂.comp (Polynomial.X + b₁)) + b₁, ?_⟩
    intro D X hX
    obtain ⟨g, hgsel, hgmem⟩ := h₁ D X hX
    let Z : Set (Fin (p + n) → ℝ) := {w | Fin.snoc w (g w) ∈ X}
    have hZ : Z ∈ S.Ω (max F a₁ + 2) ((Polynomial.X + b₁).eval D) (p + n) := by
      have hxg : X ∩ WilkiesDesign.graphOf g ∈
          S.Ω (max F a₁ + 1) (D + b₁.eval D) (p + n + 1) :=
        pair_mem (S := S) hX hgmem
      have hp := S.proj hxg
      rw [projLast_inter_graphOf X g] at hp
      rw [Polynomial.eval_add, Polynomial.eval_X]
      exact hp
    obtain ⟨h, hhsel, hhmem⟩ := h₂ ((Polynomial.X + b₁).eval D) Z hZ
    have hhmem' : gset h ∈ S.Ω a₂ ((b₂.comp (Polynomial.X + b₁)).eval D) (p + n) := by
      rw [Polynomial.eval_comp]
      exact hhmem
    refine ⟨fun l : Fin p → ℝ => Fin.snoc (h l) (g (Fin.append l (h l))), ?_, ?_⟩
    · intro l hy
      obtain ⟨y, hyX⟩ := hy
      have hfib : ∃ t : ℝ, Fin.snoc (Fin.append l (Fin.init y)) t ∈ X := by
        refine ⟨y (Fin.last n), ?_⟩
        have hs : Fin.snoc (Fin.append l (Fin.init y)) (y (Fin.last n)) = Fin.append l y := by
          rw [← Fin.append_snoc, Fin.snoc_init_self]
        rw [hs]
        exact hyX
      have hw0 : Fin.append l (Fin.init y) ∈ Z := hgsel (Fin.append l (Fin.init y)) hfib
      have hhl : Fin.append l (h l) ∈ Z := hhsel l ⟨Fin.init y, hw0⟩
      rw [show Fin.append l (Fin.snoc (h l) (g (Fin.append l (h l))))
          = Fin.snoc (Fin.append l (h l)) (g (Fin.append l (h l))) from
        Fin.append_snoc l (h l) (g (Fin.append l (h l)))]
      exact hhl
    · have hlift : {z : Fin (p + (n + 1)) → ℝ | Fin.init z ∈ gset h} ∈
          S.Ω (a₂ + 1) ((b₂.comp (Polynomial.X + b₁)).eval D) (p + n + 1) :=
        Omega.prodRight_mem hhmem'
      have hA : ({z : Fin (p + (n + 1)) → ℝ | Fin.init z ∈ gset h} ∩
          WilkiesDesign.graphOf g) ∈
          S.Ω (max (a₂ + 1) a₁ + 1) (((b₂.comp (Polynomial.X + b₁)) + b₁).eval D)
            (p + n + 1) := by
        rw [Polynomial.eval_add]
        exact pair_mem (S := S) hlift hgmem
      have hEq : ({z : Fin (p + (n + 1)) → ℝ | Fin.init z ∈ gset h} ∩
          WilkiesDesign.graphOf g)
          = gset (fun l : Fin p → ℝ => Fin.snoc (h l) (g (Fin.append l (h l)))) := by
        rw [show ({z : Fin (p + (n + 1)) → ℝ | Fin.init z ∈ gset h} ∩
            WilkiesDesign.graphOf g)
            = {z : Fin (p + (n + 1)) → ℝ | Fin.init z ∈ gset h ∧
                z (Fin.last (p + n)) = g (Fin.init z)} from by
          ext z
          rw [Set.mem_inter_iff, mem_graphOf]
          rfl]
        ext z
        exact (gset_snoc_iff h g z).symm
      rw [hEq] at hA
      exact hA

/-! ## 4. The requested statement -/

theorem G1_choice_proved (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (F p n : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (X : Set (Fin (p + n) → ℝ)),
      X ∈ S.Ω F D (p + n) →
      ∃ f : (Fin p → ℝ) → (Fin n → ℝ),
        (∀ l : Fin p → ℝ, (∃ y, Fin.append l y ∈ X) → Fin.append l (f l) ∈ X) ∧
        {z : Fin (p + n) → ℝ | ∀ j : Fin n,
            z (Fin.natAdd p j) = f (fun i => z (Fin.castAdd n i)) j} ∈ S.Ω a (b.eval D) (p + n) := by
  obtain ⟨a, b, h⟩ := gset_aux S hcd n F p
  refine ⟨a, b, ?_⟩
  intro D X hX
  obtain ⟨f, hsel, hmem⟩ := h D X hX
  exact ⟨f, hsel, hmem⟩

end Work.WilG1.Choice
