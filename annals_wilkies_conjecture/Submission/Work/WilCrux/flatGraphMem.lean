import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4b.projCoords_mem
import Submission.Work.WilG4a.subst_mem

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilCrux

open WilkiesDesign

/-! ## Auxiliary vocabulary for the flat-sheet argument

The `a`-dimensional parameter block of `Fin (a+b+1)` is read by `Fin.castAdd (b+1)`, the
`b`-dimensional fibre block by `Fin.natAdd a ∘ Fin.castSucc`, and the value coordinate is
`Fin.last (a+b)`.  `flatE` reads the parameter block together with the value coordinate;
`fibreP` is the polynomial whose zero set is the vanishing of the whole fibre block. -/

/-- The coordinate map `Fin (a+1) → Fin (a+b+1)` reading the `a` parameters and the value
coordinate, i.e. forgetting the `b` fibre coordinates. -/
def flatE (a b : ℕ) : Fin (a+1) → Fin (a+b+1) :=
  Fin.addCases (fun i : Fin a => Fin.castAdd (b+1) i) (fun _ : Fin 1 => Fin.last (a+b))

theorem flatE_castSucc {a b : ℕ} (i : Fin a) :
    flatE a b (Fin.castSucc i) = Fin.castAdd (b+1) i := by
  simp only [flatE]
  rw [show (Fin.castSucc i : Fin (a+1)) = Fin.castAdd 1 i from rfl]
  exact Fin.addCases_left i

theorem flatE_last {a b : ℕ} : flatE a b (Fin.last a) = Fin.last (a+b) := by
  simp only [flatE]
  rw [show (Fin.last a : Fin (a+1)) = Fin.natAdd a (0 : Fin 1) from rfl]
  exact Fin.addCases_right (0 : Fin 1)

/-- `∑ j, X_j^2` over the `b` fibre coordinates; its zero set is exactly the vanishing of the
whole fibre block. -/
def fibreP (a b : ℕ) : MvPolynomial (Fin (a+b+1)) ℝ :=
  ∑ j : Fin b,
    (MvPolynomial.X (Fin.natAdd a (Fin.castSucc j)) : MvPolynomial (Fin (a+b+1)) ℝ)^2

theorem eval_fibreP {a b : ℕ} (u : Fin (a+b+1) → ℝ) :
    MvPolynomial.eval u (fibreP a b) = 0 ↔
      ∀ j : Fin b, u (Fin.natAdd a (Fin.castSucc j)) = 0 := by
  rw [show MvPolynomial.eval u (fibreP a b)
        = ∑ j : Fin b, (u (Fin.natAdd a (Fin.castSucc j)))^2 from by
      simp only [fibreP, map_sum, map_pow, MvPolynomial.eval_X]]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)]
  constructor
  · intro h j; exact sq_eq_zero_iff.mp (h j (Finset.mem_univ j))
  · intro h j _; simp [h j]

/-- `famGraph G` written in the coordinate blocks of `Fin (a+b+1)`. -/
theorem famGraph_eq {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) :
    WilkiesDesign.CG.famGraph G =
      {u : Fin (a+b+1) → ℝ |
        u (Fin.last (a+b)) = G (fun i : Fin a => u (Fin.castAdd (b+1) i))
          (fun j : Fin b => u (Fin.natAdd a (Fin.castSucc j)))} := by
  ext u
  simp only [WilkiesDesign.CG.famGraph, WilkiesDesign.graphOf, Set.mem_ofPred_eq]
  constructor <;> intro h <;> rw [h] <;> congr 2

/-- The coordinate image of `famGraph G` restricted to the vanishing of the fibre block is
exactly the graph of the flat sheet `w ↦ G w 0`. -/
theorem coordImage_eq {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) :
    {y : Fin (a+1) → ℝ | ∃ x : Fin (a+b+1) → ℝ,
        x ∈ WilkiesDesign.CG.famGraph G ∩ {u | MvPolynomial.eval u (fibreP a b) = 0} ∧
        y = x ∘ flatE a b}
      = WilkiesDesign.graphOf (fun w : Fin a → ℝ => G w 0) := by
  ext y
  simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, hy⟩
    rw [Set.mem_inter_iff] at hx
    obtain ⟨hxG, hxZ⟩ := hx
    have hxZ' : ∀ j : Fin b, x (Fin.natAdd a (Fin.castSucc j)) = 0 := by
      have h : MvPolynomial.eval x (fibreP a b) = 0 := by
        simpa only [Set.mem_ofPred_eq] using hxZ
      rw [eval_fibreP] at h
      exact h
    have hlast : y (Fin.last a) = x (Fin.last (a+b)) := by
      rw [hy]; simp only [Function.comp_apply, flatE_last]
    have hinit : Fin.init y = (fun i : Fin a => x (Fin.castAdd (b+1) i)) := by
      funext i
      show y (Fin.castSucc i) = x (Fin.castAdd (b+1) i)
      rw [hy]; simp only [Function.comp_apply, flatE_castSucc]
    have hxG' : x (Fin.last (a+b)) = G (fun i : Fin a => x (Fin.castAdd (b+1) i))
        (fun j : Fin b => x (Fin.natAdd a (Fin.castSucc j))) := by
      simpa only [famGraph_eq, Set.mem_ofPred_eq] using hxG
    rw [hlast, hinit, hxG']
    congr 1
    funext j
    exact hxZ' j
  · intro hy
    let x : Fin (a+b+1) → ℝ :=
      Fin.snoc (α := fun _ => ℝ) (Fin.append (Fin.init y) (0 : Fin b → ℝ)) (y (Fin.last a))
    have hx_last : x (Fin.last (a+b)) = y (Fin.last a) := by
      simp only [x]; rw [Fin.snoc_last]
    have hx_c1 : ∀ i : Fin a, x (Fin.castAdd (b+1) i) = Fin.init y i := by
      intro i
      simp only [x]
      rw [show (Fin.castAdd (b+1) i : Fin (a+b+1)) = Fin.castSucc (Fin.castAdd b i) from
        (Fin.castSucc_castAdd i).symm]
      rw [Fin.snoc_castSucc, Fin.append_left]
    have hx_c2 : ∀ j : Fin b, x (Fin.natAdd a (Fin.castSucc j)) = 0 := by
      intro j
      simp only [x]
      rw [show (Fin.natAdd a (Fin.castSucc j) : Fin (a+b+1))
          = Fin.castSucc (Fin.natAdd a j) from rfl]
      rw [Fin.snoc_castSucc, Fin.append_right]
      exact Pi.zero_apply j
    have hx_e1 : ∀ i : Fin a, x (flatE a b (Fin.castSucc i)) = y (Fin.castSucc i) := by
      intro i; rw [flatE_castSucc]; exact hx_c1 i
    have hx_e2 : x (flatE a b (Fin.last a)) = y (Fin.last a) := by
      rw [flatE_last]; exact hx_last
    refine ⟨x, ?_, ?_⟩
    · rw [Set.mem_inter_iff]
      constructor
      · rw [famGraph_eq]
        simp only [Set.mem_ofPred_eq]
        have hA : (fun i : Fin a => x (Fin.castAdd (b+1) i)) = Fin.init y :=
          funext fun i => hx_c1 i
        have hB : (fun j : Fin b => x (Fin.natAdd a (Fin.castSucc j))) = 0 :=
          funext fun j => hx_c2 j
        rw [hA, hB, hx_last]
        exact hy
      · simp only [Set.mem_ofPred_eq]
        rw [eval_fibreP]
        intro j
        exact hx_c2 j
    · funext k
      rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
      · exact (hx_e1 i).symm
      · exact (hx_e2).symm

/-- **The flat sheet of a definable family is definable.**  If the graph of the family
`G : ℝ^a → ℝ^b → ℝ` is an `Ω`-set (format `F`, degree `D`, dimension `a+b+1`), then the graph of
the flat-sheet function `w ↦ G w 0` is again an `Ω`-set of dimension `a+1` (for some format and
degree, depending only on `a`, `b`, `F`, `D`). -/
theorem flatGraphMem (S : WilkiesDesign.SOMin) {a b F D : ℕ}
    (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1)) :
    ∃ F' D' : ℕ, WilkiesDesign.graphOf (fun w : Fin a → ℝ => G w 0) ∈ S.Ω F' D' (a + 1) := by
  set Z : Set (Fin (a+b+1) → ℝ) := {u | MvPolynomial.eval u (fibreP a b) = 0} with hZdef
  have hZ : Z ∈ S.Ω (a+b+1) (fibreP a b).totalDegree (a+b+1) := by
    rw [hZdef]; exact S.hyp (a+b+1) (fibreP a b)
  have hG' : WilkiesDesign.CG.famGraph G ∈ S.Ω (max F (a+b+1)) D (a+b+1) :=
    Work.WilG4a.mem_mono hG (le_max_left _ _) le_rfl
  have hZ' : Z ∈ S.Ω (max F (a+b+1)) (fibreP a b).totalDegree (a+b+1) :=
    Work.WilG4a.mem_mono hZ (le_max_right _ _) le_rfl
  have hX : (WilkiesDesign.CG.famGraph G ∩ Z) ∈
      S.Ω (max F (a+b+1) + 1) (D + (fibreP a b).totalDegree) (a+b+1) := by
    have h := S.inter (F := max F (a+b+1))
        (fun i : Fin 2 => if i = 0 then D else (fibreP a b).totalDegree)
        (fun i : Fin 2 => if i = 0 then WilkiesDesign.CG.famGraph G else Z)
        (by intro i
            fin_cases i
            · simpa using hG'
            · simpa using hZ')
    rw [show (∑ i : Fin 2, (if i = 0 then D else (fibreP a b).totalDegree))
        = D + (fibreP a b).totalDegree from by rw [Fin.sum_univ_two]; norm_num] at h
    rwa [Work.WilG4a.iInter_fin_two (WilkiesDesign.CG.famGraph G) Z] at h
  obtain ⟨K, p, hp⟩ := Work.WilG4b.projCoords_mem S (flatE a b)
  have himg := hp (max F (a+b+1) + 1) (D + (fibreP a b).totalDegree)
    (WilkiesDesign.CG.famGraph G ∩ Z) hX
  refine ⟨(max F (a+b+1) + 1) + K, p.eval (D + (fibreP a b).totalDegree), ?_⟩
  rw [← coordImage_eq (a := a) (b := b) G]
  rw [hZdef] at himg
  exact himg

end Work.WilCrux
