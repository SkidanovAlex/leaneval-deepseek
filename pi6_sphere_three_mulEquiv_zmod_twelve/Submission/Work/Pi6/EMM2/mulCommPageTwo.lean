import Mathlib
import Submission.Work.Pi6.EMM2.Statements
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 1000000

namespace Work.Pi6.EMM2

open CategoryTheory CategoryTheory.Limits

/-- Graded commutativity of the cup product over `ZMod 2`, as a heterogeneous equality between
the two spellings of the total degree.  In characteristic two the sign `(-1)^{nm}` is `1`. -/
theorem heq_cup (X : Type) [TopologicalSpace X] (n m : ℕ)
    (x : Work.Pi6.Coh (ZMod 2) X n) (y : Work.Pi6.Coh (ZMod 2) X m) :
    HEq (Work.Pi6.cup (ZMod 2) X n m x y) (Work.Pi6.cup (ZMod 2) X m n y x) := by
  have gc := Work.Cohomology.gradedComm (ZMod 2) (TopCat.toSSet.obj (TopCat.of X)) n m x y
  rw [show ((-1 : ZMod 2) ^ (n * m)) = 1 from by
    rw [show (-1 : ZMod 2) = 1 from CharTwo.neg_eq 1]; exact one_pow _] at gc
  rw [one_smul] at gc
  exact (eqRec_heq (φ := fun k => (Work.Pi6.Coh (ZMod 2) X k : Type)) (Nat.add_comm n m)
    (Work.Pi6.cup (ZMod 2) X n m x y)).symm.trans (heq_of_eq gc)

/-- The product on a fixed page of the spectral sequence does not depend on the spelling of the
total bidegree: `mul` is a single dependent function of `c`. -/
theorem heq_mul_reindex {𝕜 : Type} [Field 𝕜] (S : Work.Pi6.CohSS 𝕜) (r : ℕ) (a b : ℤ × ℤ)
    {c c' : ℤ × ℤ} (hc : c = c') (h : a + b = c) (h' : a + b = c')
    (x : S.E r a) (y : S.E r b) :
    HEq (S.mul r a b c h x y) (S.mul r a b c' h' x y) := by
  cases hc
  exact heq_of_eq (S.mul_congr r a b c h h' x y)

/-- The `E₂`-isomorphism of the Serre spectral sequence is a single function of the *pair* of
degrees, so its inverse maps are compatible with the canonical transport of the bidegree. -/
theorem e2inv_heq {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : ContinuousMap E B) (e₀ : E) (N : ℕ) (S : Work.Pi6.CohSS (ZMod 2))
    (hS : Work.Pi6.IsSerreMSS S p e₀ N)
    (n m n' m' : ℕ) (hn : n = n') (hm : m = m')
    (hnN : n ≤ N) (hmN : m ≤ N) (hn'N : n' ≤ N) (hm'N : m' ≤ N)
    (x : TensorProduct (ZMod 2) (Work.Pi6.Coh (ZMod 2) B n)
          (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) m))
    (x' : TensorProduct (ZMod 2) (Work.Pi6.Coh (ZMod 2) B n')
          (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) m'))
    (hx : HEq x x') :
    HEq ((Classical.choose hS n m hnN hmN).inv.hom x)
        ((Classical.choose hS n' m' hn'N hm'N).inv.hom x') := by
  cases hn
  cases hm
  have hx' : x = x' := eq_of_heq hx
  subst hx'
  rw [Subsingleton.elim hnN hn'N, Subsingleton.elim hmN hm'N]

/-- The pure tensors of the two cup products are heterogeneously equal across the two spellings
of the bidegree. -/
theorem heq_tmul_cups {B F : Type} [TopologicalSpace B] [TopologicalSpace F] (n m p r : ℕ)
    (b : Work.Pi6.Coh (ZMod 2) B n) (b' : Work.Pi6.Coh (ZMod 2) B m)
    (f : Work.Pi6.Coh (ZMod 2) F p) (f' : Work.Pi6.Coh (ZMod 2) F r) :
    HEq (Work.Pi6.cup (ZMod 2) B n m b b' ⊗ₜ[ZMod 2] Work.Pi6.cup (ZMod 2) F p r f f')
        (Work.Pi6.cup (ZMod 2) B m n b' b ⊗ₜ[ZMod 2] Work.Pi6.cup (ZMod 2) F r p f' f) := by
  have h1 := heq_cup B n m b b'
  have h2 := heq_cup F p r f f'
  grind

/-- **The product on page two is commutative on pure tensors.** -/
theorem mulCommPageTwo {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : ContinuousMap E B) (e₀ : E) (N : ℕ) (S : Work.Pi6.CohSS (ZMod 2))
    (hS : Work.Pi6.IsSerreMSS S p e₀ N)
    (s q s' q' : ℕ) (hs : s + s' ≤ N) (hq : q + q' ≤ N)
    (b : Work.Pi6.Coh (ZMod 2) B s) (f : Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) q)
    (b' : Work.Pi6.Coh (ZMod 2) B s') (f' : Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) q') :
    S.mul 2 ((s : ℤ), (q : ℤ)) ((s' : ℤ), (q' : ℤ)) (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ))
        (by ext <;> simp)
        ((Classical.choose hS s q (by omega) (by omega)).inv.hom (b ⊗ₜ f))
        ((Classical.choose hS s' q' (by omega) (by omega)).inv.hom (b' ⊗ₜ f')) =
      S.mul 2 ((s' : ℤ), (q' : ℤ)) ((s : ℤ), (q : ℤ)) (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ))
        (by ext <;> simp [add_comm])
        ((Classical.choose hS s' q' (by omega) (by omega)).inv.hom (b' ⊗ₜ f'))
        ((Classical.choose hS s q (by omega) (by omega)).inv.hom (b ⊗ₜ f)) := by
  have hmul := (Classical.choose_spec hS).1
  have hA := hmul s q s' q' b f b' f' hs hq
  have hB := hmul s' q' s q b' f' b f (by omega) (by omega)
  have hsign1 : ((-1 : ZMod 2) ^ (q * s')) = 1 := by
    rw [show (-1 : ZMod 2) = 1 from CharTwo.neg_eq 1]; exact one_pow _
  have hsign2 : ((-1 : ZMod 2) ^ (q' * s)) = 1 := by
    rw [show (-1 : ZMod 2) = 1 from CharTwo.neg_eq 1]; exact one_pow _
  rw [hsign1, one_smul] at hA
  rw [hsign2, one_smul] at hB
  have htl := heq_tmul_cups (B := B) (F := Work.StemsB.fibre p (p e₀)) s s' q q' b b' f f'
  -- (i) the goal's left-hand side is the left-hand side of the instance `hA`
  have hL : (S.mul 2 ((s : ℤ), (q : ℤ)) ((s' : ℤ), (q' : ℤ))
        (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ))
        (by ext <;> simp)
        ((Classical.choose hS s q (by omega) (by omega)).inv.hom (b ⊗ₜ f))
        ((Classical.choose hS s' q' (by omega) (by omega)).inv.hom (b' ⊗ₜ f'))) =
      ((Classical.choose hS (s + s') (q + q') hs hq).inv.hom
        (Work.Pi6.cup (ZMod 2) B s s' b b' ⊗ₜ[ZMod 2]
          Work.Pi6.cup (ZMod 2) (Work.StemsB.fibre p (p e₀)) q q' f f')) := hA
  -- (ii) the crux: the two `E₂`-inverses agree across the two spellings of the bidegree
  have hcrux : HEq ((Classical.choose hS (s + s') (q + q') hs hq).inv.hom
        (Work.Pi6.cup (ZMod 2) B s s' b b' ⊗ₜ[ZMod 2]
          Work.Pi6.cup (ZMod 2) (Work.StemsB.fibre p (p e₀)) q q' f f'))
      ((Classical.choose hS (s' + s) (q' + q) (by omega) (by omega)).inv.hom
        (Work.Pi6.cup (ZMod 2) B s' s b' b ⊗ₜ[ZMod 2]
          Work.Pi6.cup (ZMod 2) (Work.StemsB.fibre p (p e₀)) q' q f' f)) :=
    e2inv_heq p e₀ N S hS (s + s') (q + q') (s' + s) (q' + q)
      (Nat.add_comm s s') (Nat.add_comm q q') hs hq (by omega) (by omega) _ _ htl
  -- (iii) the goal's right-hand side is the `(s' + s)`-spelling of the reversed product
  have hR1 : HEq (S.mul 2 ((s' : ℤ), (q' : ℤ)) ((s : ℤ), (q : ℤ))
        (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ))
        (by ext <;> simp [add_comm])
        ((Classical.choose hS s' q' (by omega) (by omega)).inv.hom (b' ⊗ₜ f'))
        ((Classical.choose hS s q (by omega) (by omega)).inv.hom (b ⊗ₜ f)))
      (S.mul 2 ((s' : ℤ), (q' : ℤ)) ((s : ℤ), (q : ℤ))
        (((s' + s : ℕ) : ℤ), ((q' + q : ℕ) : ℤ))
        (by ext <;> simp)
        ((Classical.choose hS s' q' (by omega) (by omega)).inv.hom (b' ⊗ₜ f'))
        ((Classical.choose hS s q (by omega) (by omega)).inv.hom (b ⊗ₜ f))) :=
    heq_mul_reindex S 2 ((s' : ℤ), (q' : ℤ)) ((s : ℤ), (q : ℤ))
      (hc := by ext <;> push_cast <;> ring) (h := by ext <;> simp [add_comm])
      (h' := by ext <;> simp) _ _
  -- (iv) the instance `hB` rewrites that reversed product
  have hR2 : HEq (S.mul 2 ((s' : ℤ), (q' : ℤ)) ((s : ℤ), (q : ℤ))
        (((s' + s : ℕ) : ℤ), ((q' + q : ℕ) : ℤ))
        (by ext <;> simp)
        ((Classical.choose hS s' q' (by omega) (by omega)).inv.hom (b' ⊗ₜ f'))
        ((Classical.choose hS s q (by omega) (by omega)).inv.hom (b ⊗ₜ f)))
      ((Classical.choose hS (s' + s) (q' + q) (by omega) (by omega)).inv.hom
        (Work.Pi6.cup (ZMod 2) B s' s b' b ⊗ₜ[ZMod 2]
          Work.Pi6.cup (ZMod 2) (Work.StemsB.fibre p (p e₀)) q' q f' f)) :=
    heq_of_eq hB
  exact eq_of_heq ((heq_of_eq hL).trans (hcrux.trans (hR2.symm.trans hR1.symm)))

end Work.Pi6.EMM2
