import Mathlib
import Submission.Work.Peluse.PET.cubeTerm_snoc
import Submission.Work.Peluse.PET.cubeTermZ_eq_zero
import Submission.Work.Peluse.PET.sum_tuple_snoc_ball

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.PET

noncomputable section


/-! ## The lower-dimensional cube term -/

/-- The cube term of order `n` based at `u` with the two shift tuples `hs`, `hs'`:
`∏_{τ : Fin n → Bool} C^{|τ|} h (u + cornerShift hs hs' τ)`. -/
def redCubeLast {n : ℕ} {Q : Fin (n + 1) → Finset ℤ}
    (hs hs' : (i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}) (h : ℤ → ℂ) (u : ℤ) : ℂ :=
  ∏ τ : Fin n → Bool,
    (star^[Work.Peluse.weight τ])
      (h (u + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ))

/-- The value function of `Fin.snoc` on the subtypes. -/
private lemma snocCoe {n : ℕ} {Q : Fin (n + 1) → Finset ℤ}
    (hs : (i : Fin n) → {x : ℤ // x ∈ Q i.castSucc})
    (a : {y : ℤ // y ∈ Q (Fin.last n)}) :
    (fun i : Fin (n + 1) =>
        (Fin.snoc (α := fun i : Fin (n + 1) => {x : ℤ // x ∈ Q i}) hs a i).1)
      = Fin.snoc (fun i : Fin n => (hs i).1) a.1 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last, Fin.snoc_last]
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]

theorem prodCubeSum_last_split {n : ℕ} (Q : Fin (n + 1) → Finset ℤ) (S : Finset ℤ) (h : ℤ → ℂ)
    (hfs : Work.Peluse.FinSuppZ h) :
    Work.Peluse.prodCubeSum (n + 1) Q S (fun _ => h)
      = (((S.card : ℝ))⁻¹ * (∏ i : Fin (n + 1), (((Q i).card : ℝ))⁻¹)
          * (∏ i : Fin (n + 1), (((Q i).card : ℝ))⁻¹)
          * ∑ p : ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}) × ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}),
              ∑' x : ℤ, ‖∑ a : {x : ℤ // x ∈ Q (Fin.last n)},
                ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ])
                  (h (x + a.1 + Work.Peluse.cornerShift (fun i => (p.1 i).1) (fun i => (p.2 i).1) τ))‖ ^ 2
        : ℂ) := by
  classical
  obtain ⟨N, hN⟩ := hfs
  -- The pointwise identity: expanding the squared modulus of the inner sum over the last
  -- coordinate gives back the cube term, split along the last coordinate.
  have hpoint : ∀ (hs hs' : (i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}) (x : ℤ),
      (∑ a : {y : ℤ // y ∈ Q (Fin.last n)}, ∑ b : {y : ℤ // y ∈ Q (Fin.last n)},
          Work.Peluse.BoxNorm.cubeTermZ Q h (Fin.snoc hs a) (Fin.snoc hs' b) x)
        = ((‖∑ a : {y : ℤ // y ∈ Q (Fin.last n)}, redCubeLast hs hs' h (x + a.1)‖ ^ 2 : ℝ) : ℂ) := by
    intro hs hs' x
    have hpt : ∀ (a b : {y : ℤ // y ∈ Q (Fin.last n)}),
        Work.Peluse.BoxNorm.cubeTermZ Q h (Fin.snoc hs a) (Fin.snoc hs' b) x
          = redCubeLast hs hs' h (x + b.1) * star (redCubeLast hs hs' h (x + a.1)) := by
      intro a b
      rw [Work.Peluse.BoxNorm.cubeTermZ, snocCoe hs a, snocCoe hs' b, cubeTerm_snoc]
      simp only [redCubeLast]
    calc (∑ a : {y : ℤ // y ∈ Q (Fin.last n)}, ∑ b : {y : ℤ // y ∈ Q (Fin.last n)},
            Work.Peluse.BoxNorm.cubeTermZ Q h (Fin.snoc hs a) (Fin.snoc hs' b) x)
        = ∑ a : {y : ℤ // y ∈ Q (Fin.last n)}, ∑ b : {y : ℤ // y ∈ Q (Fin.last n)},
            redCubeLast hs hs' h (x + b.1) * star (redCubeLast hs hs' h (x + a.1)) :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hpt a b))
      _ = ((‖∑ a : {y : ℤ // y ∈ Q (Fin.last n)}, redCubeLast hs hs' h (x + a.1)‖ ^ 2 : ℝ) : ℂ) :=
          Work.Peluse.BoxNorm.sum_pairs_star_eq_normSq _
  -- the cube term vanishes off the ball
  have hvanR : ∀ (hs hs' : (i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}) (x : ℤ),
      x ∉ Work.Peluse.BoxNorm.ball (n + 1) Q N →
      ‖∑ a : {y : ℤ // y ∈ Q (Fin.last n)}, redCubeLast hs hs' h (x + a.1)‖ ^ 2 = 0 := by
    intro hs hs' x hx
    have h1 : ((‖∑ a : {y : ℤ // y ∈ Q (Fin.last n)}, redCubeLast hs hs' h (x + a.1)‖ ^ 2 : ℝ)
        : ℂ) = 0 := by
      rw [← hpoint hs hs' x]
      refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
      exact cubeTermZ_eq_zero Q h hN (Fin.snoc hs a) (Fin.snoc hs' b) hx
    exact Complex.ofReal_eq_zero.mp h1
  have hbox : Work.Peluse.prodCubeSum (n + 1) Q S (fun _ => h)
      = Work.Peluse.boxSumPow (n + 1) Q S h := rfl
  have hstep1 : Work.Peluse.BoxNorm.rawSum (n + 1) Q h
      = ∑ h₁ : (i : Fin (n + 1)) → {x : ℤ // x ∈ Q i},
          ∑ h₂ : (i : Fin (n + 1)) → {x : ℤ // x ∈ Q i},
            ∑ x ∈ Work.Peluse.BoxNorm.ball (n + 1) Q N,
              Work.Peluse.BoxNorm.cubeTermZ Q h h₁ h₂ x := by
    rw [Work.Peluse.BoxNorm.rawSum]
    simp only [Work.Peluse.BoxNorm.cubeTermZ]
    refine Finset.sum_congr rfl (fun h₁ _ => Finset.sum_congr rfl (fun h₂ _ => ?_))
    exact Work.Peluse.BoxNorm.cubeTerm_tsum_finite Q h hN h₁ h₂
  have hstep2 : (∑ h₁ : (i : Fin (n + 1)) → {x : ℤ // x ∈ Q i},
        ∑ h₂ : (i : Fin (n + 1)) → {x : ℤ // x ∈ Q i},
          ∑ x ∈ Work.Peluse.BoxNorm.ball (n + 1) Q N,
            Work.Peluse.BoxNorm.cubeTermZ Q h h₁ h₂ x)
      = ∑ hs : (i : Fin n) → {x : ℤ // x ∈ Q i.castSucc},
          ∑ hs' : (i : Fin n) → {x : ℤ // x ∈ Q i.castSucc},
            ∑ x ∈ Work.Peluse.BoxNorm.ball (n + 1) Q N,
              ((‖∑ a : {y : ℤ // y ∈ Q (Fin.last n)}, redCubeLast hs hs' h (x + a.1)‖ ^ 2 : ℝ) : ℂ) := by
    refine (sum_tuple_snoc_ball Q h N).trans ?_
    refine Finset.sum_congr rfl (fun hs _ => Finset.sum_congr rfl (fun hs' _ => ?_))
    exact Finset.sum_congr rfl (fun x _ => hpoint hs hs' x)
  have hstep3 : (∑ hs : (i : Fin n) → {x : ℤ // x ∈ Q i.castSucc},
        ∑ hs' : (i : Fin n) → {x : ℤ // x ∈ Q i.castSucc},
          ∑ x ∈ Work.Peluse.BoxNorm.ball (n + 1) Q N,
            ((‖∑ a : {y : ℤ // y ∈ Q (Fin.last n)}, redCubeLast hs hs' h (x + a.1)‖ ^ 2 : ℝ) : ℂ))
      = ((∑ p : ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc})
              × ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}),
            ∑ x ∈ Work.Peluse.BoxNorm.ball (n + 1) Q N,
              ‖∑ a : {y : ℤ // y ∈ Q (Fin.last n)}, redCubeLast p.1 p.2 h (x + a.1)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun hs _ => Finset.sum_congr rfl (fun hs' _ => ?_))
    rw [Complex.ofReal_sum]
  have hstep4 : ((∑ p : ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc})
              × ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}),
            ∑ x ∈ Work.Peluse.BoxNorm.ball (n + 1) Q N,
              ‖∑ a : {y : ℤ // y ∈ Q (Fin.last n)}, redCubeLast p.1 p.2 h (x + a.1)‖ ^ 2 : ℝ) : ℂ)
      = ((∑ p : ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc})
              × ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}),
            ∑' x : ℤ,
              ‖∑ a : {y : ℤ // y ∈ Q (Fin.last n)}, redCubeLast p.1 p.2 h (x + a.1)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_inj]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    exact (tsum_eq_sum (s := Work.Peluse.BoxNorm.ball (n + 1) Q N)
      (fun x hx => hvanR p.1 p.2 x hx)).symm
  have key : Work.Peluse.BoxNorm.rawSum (n + 1) Q h
      = ((∑ p : ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc})
              × ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}),
            ∑' x : ℤ,
              ‖∑ a : {y : ℤ // y ∈ Q (Fin.last n)}, redCubeLast p.1 p.2 h (x + a.1)‖ ^ 2 : ℝ) : ℂ) :=
    hstep1.trans (hstep2.trans (hstep3.trans hstep4))
  rw [hbox, Work.Peluse.BoxNorm.boxSumPow_eq_scaling, key]
  rw [show (∑ p : ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc})
              × ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}),
            ∑' x : ℤ,
              ‖∑ a : {y : ℤ // y ∈ Q (Fin.last n)}, redCubeLast p.1 p.2 h (x + a.1)‖ ^ 2 : ℝ)
      = (∑ p : ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc})
              × ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}),
            ∑' x : ℤ, ‖∑ a : {x : ℤ // x ∈ Q (Fin.last n)},
                ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ])
                  (h (x + a.1 + Work.Peluse.cornerShift (fun i => (p.1 i).1) (fun i => (p.2 i).1) τ))‖ ^ 2
        : ℝ) from rfl]
  rw [show Work.Peluse.BoxNorm.boxScaling (n + 1) Q S
      = ((S.card : ℝ))⁻¹ * (∏ i : Fin (n + 1), (((Q i).card : ℝ))⁻¹)
          * (∏ i : Fin (n + 1), (((Q i).card : ℝ))⁻¹) from rfl]
  push_cast
  ring

end

end Work.Peluse.PET
