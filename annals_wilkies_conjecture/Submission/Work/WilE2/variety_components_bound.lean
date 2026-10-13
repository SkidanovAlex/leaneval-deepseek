/-
  Work.WilE2 — area E2.  `Work.WilE2.variety_components_bound` (GV Corollary 3.3).

  `VarietyBound F` (`ComponentsDefs.lean`) asks for a polynomial bound on the components of a
  Pfaffian variety `{f = 0}` cut by the cube.

  The proof splits the components of `X = cubeC k ∩ Zset c g` into

  * those meeting the frontier of the cube: each such component contains a point `w` of a face
    `{x_j = σ}` and hence a component of `X ∩ {x_j = σ}`, so the hitting set of that face
    (`face_hits`, the `(k-1)`-dimensional induction hypothesis) hits it; and
  * those contained in the interior of the cube, hit by `interior_hits`.

  The polynomials come from the recursion `Q 0 = 1`, `Q (n+1) = 2(n+1)·Q n + p_int`, which is
  monotone in `n`, so `Q F` dominates `Q k` for every `k ≤ F`.
-/
import Mathlib
import Submission.Work.WilE2.ComponentsDefs
import Submission.Work.WilE2.Genericity
import Submission.Work.WilE2.VcbDefs
import Submission.Work.WilE2.VcbTopology
import Submission.Work.WilE2.face_hits
import Submission.Work.WilE2.interior_hits

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Work.WilE2

open Classical Set
open WilkiesDesign WilkiesDesign.E

/-- The sign of the `i`-th face in a fixed coordinate direction. -/
private def faceSign (i : Fin 2) : ℝ := if i = 0 then 1 else -1

/-- `Polynomial.eval` with nonnegative coefficients is monotone in the argument. -/
private lemma vcbEvalMono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun k _ =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h k)

/-- **Base case `k = 0`.**  `Fin 0 → ℝ` is a single point, so the cube is a single point. -/
private lemma base_case (r : ℕ) (c : EAChain 0 r) (g : Finset (EAPoly 0 r)) (D : ℕ)
    (hD : (∑ f ∈ g, atomDeg f) ≤ D) :
    ∃ s : Finset (Fin 0 → ℝ), (↑s : Set (Fin 0 → ℝ)) ⊆ cubeC 0 ∩ Zset c g ∧
      s.card ≤ (1 : Polynomial ℕ).eval D ∧ Hits (cubeC 0 ∩ Zset c g) s := by
  by_cases h : (cubeC 0 ∩ Zset c g).Nonempty
  · obtain ⟨x₀, hx₀⟩ := h
    refine ⟨{x₀}, ?_, ?_, ?_⟩
    · intro y hy
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hy
      rw [hy]; exact hx₀
    · rw [Finset.card_singleton]; simp
    · intro x hx
      refine ⟨x₀, Finset.mem_singleton_self _, ?_⟩
      rw [Subsingleton.elim x x₀]
  · rw [Set.not_nonempty_iff_eq_empty] at h
    refine ⟨∅, ?_, ?_, ?_⟩
    · simp
    · rw [Finset.card_empty]; simp
    · intro x hx; rw [h] at hx; exact absurd hx (Set.notMem_empty x)

/-- **Reduction.**  The face lemma (`(k-1)`-dimensional induction) and the interior lemma
together give `VarietyBound F`. -/
theorem variety_bound_of_pieces
    (hFace : ∀ {n : ℕ} (Q : Polynomial ℕ) (F : ℕ),
      (∀ (r : ℕ) (c : EAChain n r) (g : Finset (EAPoly n r)) (D : ℕ), n + r ≤ F →
        (∑ f ∈ g, atomDeg f) ≤ D → ∃ s : Finset (Fin n → ℝ),
          (↑s : Set (Fin n → ℝ)) ⊆ cubeC n ∩ Zset c g ∧ s.card ≤ Q.eval D ∧
            Hits (cubeC n ∩ Zset c g) s) →
      ∀ (r : ℕ) (c : EAChain (n+1) r) (g : Finset (EAPoly (n+1) r)) (j : Fin (n+1)) (σ : ℝ)
        (D : ℕ), n + r ≤ F → (∑ f ∈ g, atomDeg f) ≤ D →
        ∃ s : Finset (Fin (n+1) → ℝ),
          (↑s : Set (Fin (n+1) → ℝ)) ⊆ cubeC (n+1) ∩ Zset c g ∩ {x | x j = σ} ∧
            s.card ≤ Q.eval D ∧
            Hits (cubeC (n+1) ∩ Zset c g ∩ {x | x j = σ}) s)
    (hInt : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r)
      (g : Finset (EAPoly k r)), k + r ≤ F → ∃ s : Finset (Fin k → ℝ),
        (↑s : Set (Fin k → ℝ)) ⊆ cubeC k ∩ Zset c g ∧ s.card ≤ p.eval (∑ f ∈ g, atomDeg f) ∧
        (∀ x ∈ cubeC k ∩ Zset c g ∩ interior (cubeC k),
          ∃ y ∈ s, y ∈ connectedComponentIn (cubeC k ∩ Zset c g) x))
    (F : ℕ) : VarietyBound F := by
  obtain ⟨pInt, hpInt⟩ := hInt F
  -- the polynomials of the induction, one per dimension
  set Q : ℕ → Polynomial ℕ := fun n =>
    Nat.rec (1 : Polynomial ℕ) (fun n q => Polynomial.C (2 * (n + 1)) * q + pInt) n with hQ
  have hQ_zero : Q 0 = 1 := rfl
  have hQ_succ : ∀ n, Q (n + 1) = Polynomial.C (2 * (n + 1)) * Q n + pInt := fun n => rfl
  -- monotonicity: `Q n ≤ Q (n+1)` pointwise
  have hmono : ∀ (n D : ℕ), (Q n).eval D ≤ (Q (n + 1)).eval D := by
    intro n D
    rw [hQ_succ]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    have h1 : (Q n).eval D ≤ (2 * (n + 1)) * (Q n).eval D :=
      Nat.le_mul_of_pos_left _ (by omega)
    exact le_trans h1 (Nat.le_add_right _ _)
  -- the main induction
  have main : ∀ n : ℕ, ∀ (k : ℕ), k ≤ n → ∀ (r : ℕ) (c : EAChain k r)
      (g : Finset (EAPoly k r)) (D : ℕ), k + r ≤ F → (∑ f ∈ g, atomDeg f) ≤ D →
      ∃ s : Finset (Fin k → ℝ), (↑s : Set (Fin k → ℝ)) ⊆ cubeC k ∩ Zset c g ∧
        s.card ≤ (Q n).eval D ∧ Hits (cubeC k ∩ Zset c g) s := by
    intro n
    induction n with
    | zero =>
      intro k hk r c g D hfmt hD
      have hk0 : k = 0 := by omega
      subst hk0
      obtain ⟨s, hs1, hs2, hs3⟩ := base_case r c g D hD
      exact ⟨s, hs1, by rwa [hQ_zero], hs3⟩
    | succ n ih =>
      intro k hk r c g D hfmt hD
      by_cases hle : k ≤ n
      · obtain ⟨s, hs1, hs2, hs3⟩ := ih k hle r c g D hfmt hD
        exact ⟨s, hs1, le_trans hs2 (hmono n D), hs3⟩
      · -- dimension `n+1`: faces plus interior
        have hk' : k = n + 1 := by omega
        subst hk'
        have hnr : n + r ≤ F := by omega
        have hIHn : ∀ (r' : ℕ) (c' : EAChain n r') (g' : Finset (EAPoly n r')) (D' : ℕ),
            n + r' ≤ F → (∑ f ∈ g', atomDeg f) ≤ D' →
            ∃ s : Finset (Fin n → ℝ), (↑s : Set (Fin n → ℝ)) ⊆ cubeC n ∩ Zset c' g' ∧
              s.card ≤ (Q n).eval D' ∧ Hits (cubeC n ∩ Zset c' g') s :=
          fun r' c' g' D' hf hd => ih n le_rfl r' c' g' D' hf hd
        choose sf hsf using fun (j : Fin (n+1)) (i : Fin 2) =>
          hFace (F := F) (Q n) hIHn r c g j (faceSign i) D hnr hD
        obtain ⟨sint, hsint1, hsint2, hsint3⟩ := hpInt (n+1) r c g (by omega)
        set sface : Finset (Fin (n+1) → ℝ) :=
          Finset.univ.biUnion fun j : Fin (n+1) => Finset.univ.biUnion fun i : Fin 2 => sf j i
          with hsface
        refine ⟨sface ∪ sint, ?_, ?_, ?_⟩
        · -- containment
          intro y hy
          rw [Finset.mem_coe, Finset.mem_union] at hy
          rcases hy with hy | hy
          · rw [hsface] at hy
            simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hy
            obtain ⟨j, i, hji⟩ := hy
            exact ((hsf j i).1 hji).1
          · exact hsint1 hy
        · -- cardinality
          have hcu : (sface ∪ sint).card ≤ sface.card + sint.card := Finset.card_union_le _ _
          have hcard : sface.card ≤ ∑ j : Fin (n+1), ∑ i : Fin 2, (sf j i).card := by
            rw [hsface]
            refine le_trans (Finset.card_biUnion_le) (Finset.sum_le_sum fun j _ => ?_)
            exact Finset.card_biUnion_le
          have hsum : (∑ j : Fin (n+1), ∑ i : Fin 2, (sf j i).card) ≤
              2 * (n + 1) * (Q n).eval D := by
            have h1 : ∀ j : Fin (n+1), (∑ i : Fin 2, (sf j i).card) ≤ 2 * (Q n).eval D := by
              intro j
              have h2 : (∑ _i : Fin 2, (Q n).eval D) = 2 * (Q n).eval D := by
                simp [Finset.sum_const, nsmul_eq_mul]
              rw [← h2]
              exact Finset.sum_le_sum fun i _ => (hsf j i).2.1
            calc (∑ j : Fin (n+1), ∑ i : Fin 2, (sf j i).card)
                ≤ ∑ _j : Fin (n+1), 2 * (Q n).eval D := Finset.sum_le_sum fun j _ => h1 j
              _ = (n+1) * (2 * (Q n).eval D) := by simp [Finset.sum_const, nsmul_eq_mul]
              _ = 2 * (n+1) * (Q n).eval D := by ring
          have hQeval : (Q (n+1)).eval D = 2 * (n+1) * (Q n).eval D + pInt.eval D := by
            rw [hQ_succ]
            simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
          rw [hQeval]
          have := vcbEvalMono pInt hD
          omega
        · -- hitting
          intro x hx
          obtain ⟨hxC, hxZ⟩ := hx
          have hxX : x ∈ cubeC (n+1) ∩ Zset c g := ⟨hxC, hxZ⟩
          rcases component_or_frontier (k := n+1) (c := c) (g := g) x with hfr | hint
          · -- the component meets the frontier: a face hitting set hits it
            obtain ⟨w, hwG, hwf⟩ := hfr
            obtain ⟨j, hj⟩ := frontier_cubeC_subset hwf
            have hwX : w ∈ cubeC (n+1) ∩ Zset c g := connectedComponentIn_subset _ _ hwG
            obtain ⟨i, hi⟩ : ∃ i : Fin 2, faceSign i = w j := by
              rcases hj with hj | hj
              · exact ⟨0, by rw [hj]; simp [faceSign]⟩
              · exact ⟨1, by rw [hj]; simp [faceSign]⟩
            have hhit := (hsf j i).2.2 w ⟨hwX, hi.symm⟩
            obtain ⟨y, hyf, hyconn⟩ := hhit
            refine ⟨y, ?_, ?_⟩
            · rw [Finset.mem_union, hsface]
              left
              simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
              exact ⟨j, i, hyf⟩
            · -- `y` lies in the same component of `X` as `x`
              have hyface : y ∈ cubeC (n+1) ∩ Zset c g ∩ {x | x j = faceSign i} :=
                (hsf j i).1 hyf
              have hwface : w ∈ cubeC (n+1) ∩ Zset c g ∩ {x | x j = faceSign i} := ⟨hwX, hi.symm⟩
              -- the face component of `w` is contained in the `X`-component of `w`
              have hle : connectedComponentIn
                    (cubeC (n+1) ∩ Zset c g ∩ {x | x j = faceSign i}) w ⊆
                  connectedComponentIn (cubeC (n+1) ∩ Zset c g) w :=
                (isPreconnected_connectedComponentIn
                  (F := cubeC (n+1) ∩ Zset c g ∩ {x | x j = faceSign i}) (x := w)
                  ).subset_connectedComponentIn (mem_connectedComponentIn hwface)
                  (fun z hz => (connectedComponentIn_subset _ _ hz).1)
              have hyfaceC : y ∈ connectedComponentIn
                  (cubeC (n+1) ∩ Zset c g ∩ {x | x j = faceSign i}) w := by
                rw [hyconn]; exact mem_connectedComponentIn hyface
              rw [connectedComponentIn_eq hwG]
              exact connectedComponentIn_eq (hle hyfaceC)
          · -- the component lies inside the interior: the interior hitting set hits it
            have hxint : x ∈ cubeC (n+1) ∩ Zset c g ∩ interior (cubeC (n+1)) :=
              ⟨hxX, hint (mem_connectedComponentIn hxX)⟩
            obtain ⟨y, hys, hyc⟩ := hsint3 x hxint
            exact ⟨y, Finset.mem_union_right _ hys, connectedComponentIn_eq hyc⟩
  -- assemble
  refine ⟨Q F, ?_⟩
  intro k r c g hfmt
  have h := main F k (by omega) r c g (∑ f ∈ g, atomDeg f) hfmt le_rfl
  exact ⟨h.choose, h.choose_spec.2.1, h.choose_spec.1, h.choose_spec.2.2⟩

theorem variety_components_bound
    (hE2a : ∀ F : ℕ, ∃ p : Polynomial ℕ,
      ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r) (f : Fin k → WilkiesDesign.E.EAPoly k r)
        (s : Finset (Fin k → ℝ)), k + r ≤ F →
        (∀ x ∈ s, (∀ i, WilkiesDesign.E.eaEval c (f i) x = 0) ∧
          (Matrix.of fun i j => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c j (f i)) x).det ≠ 0) →
        s.card ≤ p.eval (∑ i, WilkiesDesign.E.atomDeg (f i)))
    (hSard : ∀ (m : ℕ) (G : (Fin (m + 1) → ℝ) → (Fin m → ℝ)), ContDiff ℝ 2 G →
      ∀ (y₀ : Fin m → ℝ) (ε : ℝ), 0 < ε → ∃ y : Fin m → ℝ, dist y y₀ < ε ∧
        ∀ z, G z = y → LinearIndependent ℝ (fun a => fderiv ℝ (fun w => G w a) z))
    (F : ℕ) : Work.WilE2.VarietyBound F :=
  variety_bound_of_pieces
    (fun {n} Q F hIH => face_hits (F := F) Q hIH)
    (fun F => interior_hits hE2a hSard F)
    F

end Work.WilE2
