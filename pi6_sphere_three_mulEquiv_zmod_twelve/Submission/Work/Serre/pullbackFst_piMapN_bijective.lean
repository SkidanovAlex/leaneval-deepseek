import Mathlib
import Submission.Work.Serre.E3aDefs
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.Serre.rwPiBijectiveOfRelPiVanishing
import Submission.Work.RatHurewicz.PairFibre
import Submission.Work.Serre.cylJoinedIncl
import Submission.Work.Serre.pathConnectedSpace_homotopyFibre
import Submission.Work.RatHurewicz.homotopyFibreMap_exists
import Submission.Work.Serre.homotopyFibreMap_lift_nullhomotopy
import Submission.Work.Serre.subsingleton_homotopyFibre_of_piMapN
import Submission.Work.Serre.exists_path_pullbackFst
import Submission.Work.Serre.piMapN_monoidHom

/-!
# Base change of an `N`-connected map along a Serre fibration

If `q : E → B` is a Serre fibration and `g : Γ → B` induces a bijection on `π_i` at every base
point for every `i ≤ N`, then the base change `Work.StemsB.pullbackFst q g : Pullback q g → E` is
bijective on `π_i` for every `i < N`.  This is the standard "base change of an `N`-connected map
along a fibration is `N`-connected (one degree lower on the target)".

The proof decomposes as follows.

* `Work.Serre.subsingleton_homotopyFibre_of_piMapN` gives that the homotopy fibre of `g` at any
  point is `(N-1)`-connected.
* `Work.Serre.homotopyFibreMap_lift_nullhomotopy` says that null-homotopies lift along the
  comparison map of homotopy fibres of the pullback square, i.e. the induced map
  `π_k (homotopyFibre (pullbackFst q g) x) → π_k (homotopyFibre g (pullbackSnd q g x))` is
  injective.  Hence the homotopy fibre of `pullbackFst q g` is `(N-1)`-connected as well
  (`Work.Serre.subsingleton_homotopyFibre_of_subsingleton_homotopyFibreMap`).
* `Work.Serre.rwPiBijectiveOfRelPiVanishing` converts `(N-1)`-connectedness of the homotopy fibre
  and `π_0`-surjectivity of `pullbackFst q g` (`Work.Serre.exists_path_pullbackFst`) into
  bijectivity of `π_i(pullbackFst q g)` for `i ≤ N - 1`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre

noncomputable section

/-! ## The degree-`0` vocabulary -/

/-- A homotopy between two `0`-cubes given by the constant cubes at joined points produces a path
between those points. -/
private theorem joined_of_genLoopZero_homotopic {X : Type} [TopologicalSpace X] {x p q : X}
    (h : GenLoop.Homotopic (genLoopZero X x p) (genLoopZero X x q)) : Joined p q := by
  obtain ⟨H⟩ := h
  exact ⟨Path.mk ⟨fun t => H (t, fun _ => 0),
    H.continuous.comp (continuous_id.prodMk continuous_const)⟩
    (H.map_zero_left (fun _ => 0)) (H.map_one_left (fun _ => 0))⟩

/-- In degree `0` the class of the constant `0`-cube at `p` agrees with the class at `q` exactly
when `p` and `q` are joined by a path. -/
private theorem genLoopZero_eq_iff {X : Type} [TopologicalSpace X] {x p q : X} :
    ((⟦genLoopZero X x p⟧ : HomotopyGroup (Fin 0) X x) = ⟦genLoopZero X x q⟧) ↔ Joined p q :=
  ⟨fun h => joined_of_genLoopZero_homotopic (Quotient.exact h),
    fun h => Quotient.sound (genLoopZero_homotopic h.some)⟩

/-- Every `0`-cube is the constant `0`-cube at its value (the `0`-cube has empty boundary). -/
private theorem eq_genLoopZero {X : Type} [TopologicalSpace X] {x : X} (γ : Ω^ (Fin 0) X x) :
    γ = genLoopZero X x (γ (fun _ => 0)) := by
  apply GenLoop.ext
  intro u
  show γ u = γ (fun _ => 0)
  exact congrArg γ (Subsingleton.elim u (fun _ => 0))

/-- **Injectivity of `π₀` in geometric form.**  If the homotopy fibre of `i` over `b` is path
connected and `i b` and `i b'` are joined, then `b` and `b'` are joined. -/
private theorem joined_of_joined_image {A W : Type} [TopologicalSpace A] [TopologicalSpace W]
    (i : C(A, W)) (b b' : A)
    (h : Subsingleton (HomotopyGroup (Fin 0)
      (Work.RatHurewicz.homotopyFibre i b)
      (Work.RatHurewicz.homotopyFibreBasepoint i b))) (hb : Joined (i b) (i b')) :
    Joined b b' := by
  obtain ⟨γ⟩ := hb
  have hjoin : Joined (Work.RatHurewicz.homotopyFibreBasepoint i b)
      (⟨(b', ⟨γ.toContinuousMap, γ.source'⟩), γ.target'⟩ :
        Work.RatHurewicz.homotopyFibre i b) :=
    (genLoopZero_eq_iff (x := Work.RatHurewicz.homotopyFibreBasepoint i b)).mp (h.elim _ _)
  have hmap : Joined ((Work.RatHurewicz.homotopyFibreFst i b)
        (Work.RatHurewicz.homotopyFibreBasepoint i b))
      ((Work.RatHurewicz.homotopyFibreFst i b)
        (⟨(b', ⟨γ.toContinuousMap, γ.source'⟩), γ.target'⟩ :
          Work.RatHurewicz.homotopyFibre i b)) :=
    hjoin.map (Work.RatHurewicz.homotopyFibreFst i b).continuous
  exact hmap

/-- `π₀`-injectivity of a map whose homotopy fibre is path connected. -/
private theorem piMapN_zero_injective {A W : Type} [TopologicalSpace A] [TopologicalSpace W]
    (i : C(A, W)) (a : A)
    (h : ∀ b : A, Subsingleton (HomotopyGroup (Fin 0)
      (Work.RatHurewicz.homotopyFibre i b)
      (Work.RatHurewicz.homotopyFibreBasepoint i b))) :
    Function.Injective (piMapN i 0 a) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h γ =>
    induction y using Quotient.inductionOn with
    | h γ' =>
      obtain ⟨p⟩ : Joined (i (γ (fun _ => 0))) (i (γ' (fun _ => 0))) := by
        have h2 : (⟦genLoopZero W (i a) (i (γ (fun _ => 0)))⟧ : HomotopyGroup (Fin 0) W (i a))
            = ⟦genLoopZero W (i a) (i (γ' (fun _ => 0)))⟧ := by
          have h3 := hxy
          rw [show (⟦γ⟧ : HomotopyGroup (Fin 0) A a)
                = ⟦genLoopZero A a (γ (fun _ => 0))⟧ from congrArg _ (eq_genLoopZero γ),
            show (⟦γ'⟧ : HomotopyGroup (Fin 0) A a)
                = ⟦genLoopZero A a (γ' (fun _ => 0))⟧ from congrArg _ (eq_genLoopZero γ'),
            piMapN_zero_genLoopZero, piMapN_zero_genLoopZero] at h3
          exact h3
        exact genLoopZero_eq_iff.mp h2
      obtain ⟨p'⟩ : Joined (γ (fun _ => 0)) (γ' (fun _ => 0)) :=
        joined_of_joined_image i _ _ (h _) ⟨p⟩
      apply Quotient.sound
      rw [eq_genLoopZero γ, eq_genLoopZero γ']
      exact genLoopZero_homotopic p'

/-- `π₀`-surjectivity of a map whose image meets every path component of the target. -/
private theorem piMapN_zero_surjective {A W : Type} [TopologicalSpace A] [TopologicalSpace W]
    (i : C(A, W)) (a : A)
    (hconn : ∀ w : W, ∃ a' : A, Nonempty (Path w (i a'))) :
    Function.Surjective (piMapN i 0 a) := by
  intro z
  induction z using Quotient.inductionOn with
  | h γ =>
    obtain ⟨a', ha'⟩ := hconn (γ (fun _ => 0))
    refine ⟨⟦genLoopZero A a a'⟧, ?_⟩
    rw [piMapN_zero_genLoopZero, eq_genLoopZero γ]
    apply Quotient.sound
    exact genLoopZero_homotopic ha'.some.symm

/-- The unit of `π_{n+1}` is preserved by `piMapN`. -/
private theorem piMapN_one_succ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (x : X) :
    piMapN f (n + 1) x (1 : HomotopyGroup (Fin (n + 1)) X x) = 1 := by
  obtain ⟨F, hF⟩ := piMapN_monoidHom f (n + 1) x
  rw [← hF 1]
  exact map_one F

/-! ## The homotopy fibre of the base change -/

/-- **The homotopy fibre of `pullbackFst q g` is trivial wherever the homotopy fibre of `g` is.**
This is the consequence of the null-homotopy lifting theorem
`Work.Serre.homotopyFibreMap_lift_nullhomotopy`: null-homotopies lift along the comparison map of
homotopy fibres of the pullback square, so that comparison map is injective on every `π_k`. -/
theorem subsingleton_homotopyFibre_of_subsingleton_homotopyFibreMap {E B Γ : Type}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Γ] (q : C(E, B)) (g : C(Γ, B))
    (hq : Work.StemsB.IsSerreFibration q) (x : Work.StemsB.Pullback q g) (k : ℕ)
    (h : Subsingleton (HomotopyGroup (Fin k)
      (Work.RatHurewicz.homotopyFibre g (Work.StemsB.pullbackSnd q g x))
      (Work.RatHurewicz.homotopyFibreBasepoint g (Work.StemsB.pullbackSnd q g x)))) :
    Subsingleton (HomotopyGroup (Fin k)
      (Work.RatHurewicz.homotopyFibre (Work.StemsB.pullbackFst q g) x)
      (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst q g) x)) := by
  have hsq : q.comp (Work.StemsB.pullbackFst q g) = g.comp (Work.StemsB.pullbackSnd q g) :=
    ContinuousMap.ext (fun y => y.2)
  have hbp : Work.RatHurewicz.homotopyFibreMap (Work.StemsB.pullbackFst q g) g q
      (Work.StemsB.pullbackSnd q g) hsq x
      (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst q g) x)
      = Work.RatHurewicz.homotopyFibreBasepoint g (Work.StemsB.pullbackSnd q g x) :=
    Work.RatHurewicz.homotopyFibreMap_basepoint (Work.StemsB.pullbackFst q g) g q
      (Work.StemsB.pullbackSnd q g) hsq x
  haveI : Subsingleton (HomotopyGroup (Fin k)
      (Work.RatHurewicz.homotopyFibre g (Work.StemsB.pullbackSnd q g x))
      (Work.RatHurewicz.homotopyFibreMap (Work.StemsB.pullbackFst q g) g q
        (Work.StemsB.pullbackSnd q g) hsq x
        (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst q g) x))) :=
    hbp.symm ▸ h
  refine ⟨fun u v => ?_⟩
  induction u using Quotient.inductionOn with
  | h γ =>
    induction v using Quotient.inductionOn with
    | h δ =>
      have hV : GenLoop.Homotopic
          (Work.StemsB.genLoopMap (Work.RatHurewicz.homotopyFibreMap (Work.StemsB.pullbackFst q g)
            g q (Work.StemsB.pullbackSnd q g) hsq x) k γ)
          (GenLoop.const : GenLoop (Fin k)
            (Work.RatHurewicz.homotopyFibre g (Work.StemsB.pullbackSnd q g x))
            (Work.RatHurewicz.homotopyFibreMap (Work.StemsB.pullbackFst q g) g q
              (Work.StemsB.pullbackSnd q g) hsq x
              (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst q g) x))) :=
        Quotient.exact (Subsingleton.elim
          (α := HomotopyGroup (Fin k)
            (Work.RatHurewicz.homotopyFibre g (Work.StemsB.pullbackSnd q g x))
            (Work.RatHurewicz.homotopyFibreMap (Work.StemsB.pullbackFst q g) g q
              (Work.StemsB.pullbackSnd q g) hsq x
              (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst q g) x)))
          (Quotient.mk _ (Work.StemsB.genLoopMap (Work.RatHurewicz.homotopyFibreMap
            (Work.StemsB.pullbackFst q g) g q (Work.StemsB.pullbackSnd q g) hsq x) k γ))
          (Quotient.mk _ (GenLoop.const : GenLoop (Fin k)
            (Work.RatHurewicz.homotopyFibre g (Work.StemsB.pullbackSnd q g x))
            (Work.RatHurewicz.homotopyFibreMap (Work.StemsB.pullbackFst q g) g q
              (Work.StemsB.pullbackSnd q g) hsq x
              (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst q g) x)))))
      have hc : GenLoop.Homotopic γ (GenLoop.const : GenLoop (Fin k)
          (Work.RatHurewicz.homotopyFibre (Work.StemsB.pullbackFst q g) x)
          (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst q g) x)) :=
        homotopyFibreMap_lift_nullhomotopy q g hq hsq x k γ hV
      have hd : GenLoop.Homotopic δ (GenLoop.const : GenLoop (Fin k)
          (Work.RatHurewicz.homotopyFibre (Work.StemsB.pullbackFst q g) x)
          (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst q g) x)) :=
        homotopyFibreMap_lift_nullhomotopy q g hq hsq x k δ
          (Quotient.exact (Subsingleton.elim
            (α := HomotopyGroup (Fin k)
              (Work.RatHurewicz.homotopyFibre g (Work.StemsB.pullbackSnd q g x))
              (Work.RatHurewicz.homotopyFibreMap (Work.StemsB.pullbackFst q g) g q
                (Work.StemsB.pullbackSnd q g) hsq x
                (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst q g) x)))
            (Quotient.mk _ (Work.StemsB.genLoopMap (Work.RatHurewicz.homotopyFibreMap
              (Work.StemsB.pullbackFst q g) g q (Work.StemsB.pullbackSnd q g) hsq x) k δ))
            (Quotient.mk _ (GenLoop.const : GenLoop (Fin k)
              (Work.RatHurewicz.homotopyFibre g (Work.StemsB.pullbackSnd q g x))
              (Work.RatHurewicz.homotopyFibreMap (Work.StemsB.pullbackFst q g) g q
                (Work.StemsB.pullbackSnd q g) hsq x
                (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst q g) x))))))
      exact (Quotient.sound hc).trans (Quotient.sound hd).symm

/-- Base change of an `N`-connected map along a Serre fibration is `N`-connected.

If `q : E → B` is a Serre fibration and `g : Γ → B` is bijective on `π_i` for every `i ≤ N`, then
the projection `Work.StemsB.pullbackFst q g : Pullback q g → E` is bijective on `π_i` for `i < N`.

Route: `pullbackSnd q g : Pullback q g → Γ` is a Serre fibration (the base change of `q`,
`Work.StemsB.hasHLP_pullback`), and so is `q`; the fibre of `pullbackSnd` over `γ : Γ` is
homeomorphic to the fibre of `q` over `g γ` (via `(e,γ) ↦ e`).  The two long exact homotopy
sequences (`Work.StemsB.fibrationLES_of_isSerreFibration`) form a ladder along the maps
`pullbackFst`, `g` (on the bases) and the fibre homeomorphism (on the fibres), so the five lemma
(`Algebra.FiveLemma`, `CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono'`) gives the
claim.  Note the hypothesis is the *strong* form (bijective through degree `N`, not just below `N`):
with only `i < N` the statement is FALSE (`N = 2`, `q` the path–loop fibration of `S²`, `g` the Hopf
map `S³ → S²`: then `π₁(pullbackFst) : ℤ → 0`). -/
theorem pullbackFst_piMapN_bijective {E B Γ : Type} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace Γ] (q : C(E, B)) (g : C(Γ, B)) (hq : Work.StemsB.IsSerreFibration q)
    (N : ℕ) (hg : ∀ i : ℕ, i ≤ N → ∀ γ : Γ, Function.Bijective (Work.Serre.piMapN g i γ)) :
    ∀ i : ℕ, i < N → ∀ p : Work.StemsB.Pullback q g,
      Function.Bijective (Work.Serre.piMapN (Work.StemsB.pullbackFst q g) i p) := by
  by_cases hX : Nonempty (Work.StemsB.Pullback q g)
  · obtain ⟨x₀⟩ := hX
    have hconn0 : ∀ w : E, ∃ x : Work.StemsB.Pullback q g,
        Nonempty (Path w (Work.StemsB.pullbackFst q g x)) :=
      Work.Serre.exists_path_pullbackFst q g hq N (Work.StemsB.pullbackSnd q g x₀) hg
    intro i hi p
    have hN1 : 1 ≤ N := by omega
    have hvan : ∀ (x : Work.StemsB.Pullback q g) (k : ℕ), k ≤ N - 1 →
        Subsingleton (HomotopyGroup (Fin k)
          (Work.RatHurewicz.homotopyFibre (Work.StemsB.pullbackFst q g) x)
          (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst q g) x)) :=
      fun x k hk => subsingleton_homotopyFibre_of_subsingleton_homotopyFibreMap q g hq x k
        (Work.Serre.subsingleton_homotopyFibre_of_piMapN g N hN1 (Work.StemsB.pullbackSnd q g x)
          hg k hk)
    rcases Nat.lt_or_ge N 2 with hN2 | hN2
    · -- `N ≤ 1`, and `i < N`, so `N = 1` and `i = 0`
      have hi0 : i = 0 := by omega
      subst hi0
      refine ⟨piMapN_zero_injective (Work.StemsB.pullbackFst q g) p
          (fun b => hvan b 0 (by omega)),
        piMapN_zero_surjective (Work.StemsB.pullbackFst q g) p hconn0⟩
    · -- `2 ≤ N`: the long exact sequence argument
      exact rwPiBijectiveOfRelPiVanishing (N - 2) (Work.StemsB.pullbackFst q g) hconn0
        (fun x k hk => hvan x k (by omega))
        (fun x y => by
          haveI : Subsingleton (HomotopyGroup (Fin ((N - 2) + 1))
              (Work.RatHurewicz.homotopyFibre (Work.StemsB.pullbackFst q g) x)
              (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst q g) x)) :=
            hvan x ((N - 2) + 1) (by omega)
          exact (congrArg (piMapN
              (Work.RatHurewicz.homotopyFibreFst (Work.StemsB.pullbackFst q g) x)
              ((N - 2) + 1)
              (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst q g) x))
            (Subsingleton.elim y 1)).trans
            (piMapN_one_succ (Work.RatHurewicz.homotopyFibreFst (Work.StemsB.pullbackFst q g) x)
              (N - 2)
              (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst q g) x)))
        i (by omega) p
  · -- the pullback is empty, so the claim is vacuous
    intro i hi p
    exact absurd ⟨p⟩ hX

end

end Work.Serre
