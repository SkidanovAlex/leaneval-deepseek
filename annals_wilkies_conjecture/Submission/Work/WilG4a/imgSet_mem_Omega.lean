import Mathlib
import Submission.Work.WilG4a.ImgSetDefs
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG4a.fiber_defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a

open WilkiesDesign WilkiesConjecture

/-- `Fin.init` of `w ∘ iota1` is the first `p` coordinates of `w`, i.e. `Fin.init (Fin.init w)`. -/
theorem init_comp_iota1 (p : ℕ) (w : Fin (p + 2) → ℝ) :
    Fin.init (w ∘ iota1 p) = Fin.init (Fin.init w) := by
  funext i
  show w (iota1 p (Fin.castSucc i)) = w (Fin.castSucc (Fin.castSucc i))
  simp only [iota1, Fin.snoc_castSucc]

/-- The last coordinate of `w ∘ iota1` is the last coordinate of `w`. -/
theorem last_comp_iota1 (p : ℕ) (w : Fin (p + 2) → ℝ) :
    (w ∘ iota1 p) (Fin.last p) = w (Fin.last (p + 1)) := by
  rw [Function.comp_apply, iota1, Fin.snoc_last]

/-- `Fin.snoc (Fin.init (Fin.init w)) (w at the `y`-slot) = Fin.init w`. -/
theorem snoc_init_eq (p : ℕ) (w : Fin (p + 2) → ℝ) :
    Fin.snoc (Fin.init (Fin.init w)) (w (Fin.castSucc (Fin.last p))) = Fin.init w :=
  Fin.snoc_init_self (Fin.init w)

/-- `Fin.init` of `Fin.snoc (Fin.snoc (Fin.init z) y) s` is `Fin.snoc (Fin.init z) y`. -/
theorem init_snoc_snoc (p : ℕ) (z : Fin (p + 1) → ℝ) (y s : ℝ) :
    Fin.init ((Fin.snoc (Fin.snoc (Fin.init z) y) s : Fin (p + 2) → ℝ)) =
      Fin.snoc (Fin.init z) y := by
  rw [Fin.init_snoc]

/-- The set `{(l,y,s) | (l,y) ∈ κ}`: the cylinder over `κ` in `ℝ^{p+2}`.  It is
`liftFirst 1 κ`, since `Fin.init` forgets the last coordinate. -/
theorem cyl_eq_liftFirst (p : ℕ) (κ : Set (Fin (p + 1) → ℝ)) :
    {w : Fin (p + 2) → ℝ | Fin.init w ∈ κ} = Work.WilG5.liftFirst 1 κ := by
  ext w
  simp only [Work.WilG5.liftFirst, Set.mem_ofPred_eq]
  rw [show Fin.init w = (fun i : Fin (p + 1) => w (Fin.castAdd 1 i)) from by funext i; rfl]

/-- `imgSet κ f` is the coordinate image of `{Fin.init w ∈ κ} ∩ graphFam f` along `iota1 p`,
which selects the coordinates `(l, s)` of `(l, y, s)`. -/
theorem imgSet_eq_coordImage (p : ℕ) (κ : Set (Fin (p + 1) → ℝ))
    (f : (Fin p → ℝ) → ℝ → ℝ) :
    imgSet p κ f =
      Work.WilG5.coordImage (iota1 p) ({w : Fin (p + 2) → ℝ | Fin.init w ∈ κ} ∩ graphFam f) := by
  ext z
  constructor
  · rintro ⟨y, hyκ, hyf⟩
    refine ⟨Fin.snoc (Fin.snoc (Fin.init z) y) (z (Fin.last p)), ⟨?_, ?_⟩, ?_⟩
    · -- the cylinder condition
      simp only [Set.mem_ofPred_eq]
      rw [init_snoc_snoc]
      exact hyκ
    · -- the graph condition, via `mem_graphFam_iff`
      rw [mem_graphFam_iff]
      exact hyf.symm
    · -- the coordinate image: `iota1` keeps `l` and the last coordinate
      funext i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [Function.comp_apply, iota1, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        rfl
      · rw [Function.comp_apply, iota1, Fin.snoc_last, Fin.snoc_last]
  · rintro ⟨w, ⟨hwκ, hwg⟩, hwz⟩
    rw [mem_graphFam] at hwg
    refine ⟨w (Fin.castSucc (Fin.last p)), ?_, ?_⟩
    · -- `Fin.snoc (Fin.init z) y ∈ κ`
      rw [show Fin.init z = Fin.init (Fin.init w) from by rw [← hwz]; exact init_comp_iota1 p w,
        snoc_init_eq p w]
      exact hwκ
    · -- `f (Fin.init z) y = z (Fin.last p)`
      rw [show Fin.init z = Fin.init (Fin.init w) from by rw [← hwz]; exact init_comp_iota1 p w]
      rw [show z (Fin.last p) = w (Fin.last (p + 1)) from by rw [← hwz]; exact last_comp_iota1 p w]
      exact hwg.symm

theorem imgSet_mem_Omega (S : WilkiesDesign.SOMin) (p F0 Fκ : ℕ) (bκ : MvPolynomial (Fin 2) ℕ) :
    ∃ (A C : ℕ),
      ∀ (D : ℕ) (f : (Fin p → ℝ) → ℝ → ℝ) (κ : Set (Fin (p + 1) → ℝ)),
        Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        κ ∈ S.Ω Fκ (MvPolynomial.eval ![D, 1] bκ) (p + 1) →
        Work.WilG4a.imgSet p κ f ∈ S.Ω A (D + MvPolynomial.eval ![D, 1] bκ + C) (p + 1) := by
  refine ⟨max F0 (Fκ + 1) + 1 + 64 * ((p + 2) + (p + 1)) + 64,
    32 * ((p + 2) + (p + 1)) + 32, ?_⟩
  intro D f κ hf hκ
  rw [imgSet_eq_coordImage p κ f]
  set b : ℕ := MvPolynomial.eval ![D, 1] bκ with hb
  have hκb : κ ∈ S.Ω Fκ b (p + 1) := by rw [hb]; exact hκ
  -- the cylinder over κ
  have hLift : Work.WilG5.liftFirst 1 κ ∈ S.Ω (Fκ + 1) b ((p + 1) + 1) :=
    Work.WilG5.liftFirst_mem (S := S) 1 Fκ b hκb
  -- a common format
  have hLift' : Work.WilG5.liftFirst 1 κ ∈ S.Ω (max F0 (Fκ + 1)) b ((p + 1) + 1) :=
    Work.WilG5.mem_mono hLift _ _ (le_max_right _ _) le_rfl
  have hf' : graphFam f ∈ S.Ω (max F0 (Fκ + 1)) D ((p + 1) + 1) :=
    Work.WilG5.mem_mono hf _ _ (le_max_left _ _) le_rfl
  -- the intersection
  have hJ := S.inter (fun i : Fin 2 => if i = 0 then D else b)
    (fun i : Fin 2 => if i = 0 then graphFam f else Work.WilG5.liftFirst 1 κ)
    (by intro i; fin_cases i <;> simpa)
  rw [show (∑ i : Fin 2, if i = 0 then D else b) = D + b from by
    simp [Fin.sum_univ_two]] at hJ
  have hJset : (⋂ i : Fin 2, if i = 0 then graphFam f else Work.WilG5.liftFirst 1 κ) =
      graphFam f ∩ Work.WilG5.liftFirst 1 κ := by
    ext z; simp [Fin.forall_fin_two]
  rw [hJset] at hJ
  rw [Set.inter_comm] at hJ
  -- transport along `coordImage`
  have hC := Work.WilG5.coordImage_mem (S := S) (m := p + 1) (N := p + 2) (ι := iota1 p)
    (F := max F0 (Fκ + 1) + 1) (D := D + b) hJ
  -- the goal's cylinder is `liftFirst 1 κ`
  rw [cyl_eq_liftFirst p κ]
  -- degree and format bookkeeping
  refine Work.WilG5.mem_mono (S := S) hC _ _ le_rfl ?_
  show ((D + b) + 32 * ((p + 2) + (p + 1))) + 32 ≤ D + b + (32 * ((p + 2) + (p + 1)) + 32)
  omega

end Work.WilG4a
