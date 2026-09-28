import Mathlib
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.Models
import Submission.Work.Serre.rwPiBijectiveOfRelPiVanishing
import Submission.Work.Serre.homotopyFibreMap_lift_nullhomotopy
import Submission.Work.Serre.subsingleton_homotopyFibre_of_piMapN
import Submission.Work.Serre.exists_path_pullbackFst
import Submission.Work.RatHurewicz.homotopyFibreMap_exists
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.Serre.cylRelPi

set_option synthInstance.maxHeartbeats 400000


/-!
# The base change of a Serre fibration along a `π`-isomorphism: connectivity of the projections

For a Serre fibration `p : E → B` and a map `g : Γ → B` which is bijective on `π_i` for all `i ≤ N`,
the projection `pullbackSnd g p : Γ ×_B E → E` is bijective on `π_i` for all `i < N`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre.SPC

noncomputable section

/-! ## The swap of the two presentations of the fibre product -/

/-- The canonical homeomorphism `Γ ×_B E → E ×_B Γ` of the two presentations of the fibre product
(simply the swap of the two factors). -/
def pbSwap {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B] [TopologicalSpace E]
    (g : C(Γ, B)) (p : C(E, B)) : C(Work.StemsB.Pullback g p, Work.StemsB.Pullback p g) where
  toFun x := ⟨(x.1.2, x.1.1), x.2.symm⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_snd.prodMk continuous_fst).comp continuous_subtype_val

/-- The inverse of `pbSwap`. -/
def pbSwapInv {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B] [TopologicalSpace E]
    (g : C(Γ, B)) (p : C(E, B)) : C(Work.StemsB.Pullback p g, Work.StemsB.Pullback g p) where
  toFun y := ⟨(y.1.2, y.1.1), y.2.symm⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_snd.prodMk continuous_fst).comp continuous_subtype_val

theorem pbSwapInv_pbSwap {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) (x : Work.StemsB.Pullback g p) :
    pbSwapInv g p (pbSwap g p x) = x := rfl

theorem pbSwap_pbSwapInv {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) (y : Work.StemsB.Pullback p g) :
    pbSwap g p (pbSwapInv g p y) = y := rfl

/-- Under the swap, the first projection of `Pullback p g` becomes the second projection of
`Pullback g p`. -/
theorem pbSwap_pullbackSnd {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) :
    (Work.StemsB.pullbackFst p g).comp (pbSwap g p) = Work.StemsB.pullbackSnd g p := by
  ext x
  rfl

/-- The swap is a bijection. -/
theorem pbSwap_bijective {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) :
    Function.Bijective (pbSwap g p) :=
  ⟨fun a b h => by
     have h1 := congrArg (pbSwapInv g p) h
     simpa only [pbSwapInv_pbSwap] using h1,
   fun b => ⟨pbSwapInv g p b, pbSwap_pbSwapInv g p b⟩⟩

/-- The swap induces a bijection on every homotopy group. -/
theorem bijective_piMapN_pbSwap {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) (n : ℕ)
    (x : Work.StemsB.Pullback g p) :
    Function.Bijective (Work.Serre.piMapN (pbSwap g p) n x) := by
  have key : ∀ a : HomotopyGroup (Fin n) (Work.StemsB.Pullback g p) x,
      Work.Serre.piMapN (pbSwapInv g p) n (pbSwap g p x) (Work.Serre.piMapN (pbSwap g p) n x a)
        = a := by
    intro a
    exact (Work.Serre.piMapN_comp (pbSwap g p) (pbSwapInv g p) n x a).symm.trans
      (Work.Serre.piMapN_id n x a)
  have key' : ∀ b : HomotopyGroup (Fin n) (Work.StemsB.Pullback p g) (pbSwap g p x),
      Work.Serre.piMapN (pbSwap g p) n x
        (Work.Serre.piMapN (pbSwapInv g p) n (pbSwap g p x) b) = b := by
    intro b
    exact (Work.Serre.piMapN_comp (pbSwapInv g p) (pbSwap g p) n (pbSwap g p x) b).symm.trans
      (Work.Serre.piMapN_id n (pbSwap g p x) b)
  refine ⟨fun a b h => ?_, fun b => ⟨Work.Serre.piMapN (pbSwapInv g p) n (pbSwap g p x) b, key' b⟩⟩
  have h1 : Work.Serre.piMapN (pbSwapInv g p) n (pbSwap g p x)
      (Work.Serre.piMapN (pbSwap g p) n x a)
      = Work.Serre.piMapN (pbSwapInv g p) n (pbSwap g p x)
        (Work.Serre.piMapN (pbSwap g p) n x b) := by rw [h]
  rwa [key a, key b] at h1

/-- **`π_n` of `pullbackSnd g p` is `π_n` of `pullbackFst p g` conjugated by the swap.** -/
theorem piMapN_pullbackSnd_apply {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) (n : ℕ)
    (x : Work.StemsB.Pullback g p)
    (a : HomotopyGroup (Fin n) (Work.StemsB.Pullback g p) x) :
    Work.Serre.piMapN (Work.StemsB.pullbackSnd g p) n x a
      = Work.Serre.piMapN (Work.StemsB.pullbackFst p g) n (pbSwap g p x)
        (Work.Serre.piMapN (pbSwap g p) n x a) :=
  Work.Serre.piMapN_comp (pbSwap g p) (Work.StemsB.pullbackFst p g) n x a

/-- **The factorisation of `π_n(pullbackSnd)` through the swap.** -/
theorem piMapN_pullbackSnd_eq {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) (n : ℕ)
    (x : Work.StemsB.Pullback g p) :
    Work.Serre.piMapN (Work.StemsB.pullbackSnd g p) n x
      = (Work.Serre.piMapN (Work.StemsB.pullbackFst p g) n (pbSwap g p x)) ∘
        (Work.Serre.piMapN (pbSwap g p) n x) := by
  funext a
  simpa only [Function.comp_apply] using piMapN_pullbackSnd_apply g p n x a

/-- If the swapped projection is bijective on `π_n` at the swapped point, so is `pullbackSnd`. -/
theorem bijective_piMapN_pullbackSnd_of_fst {Γ B E : Type} [TopologicalSpace Γ]
    [TopologicalSpace B] [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) (n : ℕ)
    (x : Work.StemsB.Pullback g p)
    (h : Function.Bijective (Work.Serre.piMapN (Work.StemsB.pullbackFst p g) n (pbSwap g p x))) :
    Function.Bijective (Work.Serre.piMapN (Work.StemsB.pullbackSnd g p) n x) := by
  rw [piMapN_pullbackSnd_eq g p n x]
  exact Function.Bijective.comp h (bijective_piMapN_pbSwap g p n x)

/-! ## The homotopy fibre of the swapped projection -/

/-- The square commuted by `pullbackFst` and `pullbackSnd`. -/
theorem pbSquare {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B] [TopologicalSpace E]
    (g : C(Γ, B)) (p : C(E, B)) :
    p.comp (Work.StemsB.pullbackFst p g) = g.comp (Work.StemsB.pullbackSnd p g) :=
  ContinuousMap.ext (fun y => y.2)

/-- **The homotopy fibre of the swapped projection is `(N-1)`-connected.**  If `g` is bijective on
`π_i` for `i ≤ N` (`N ≥ 1`), then for every point `y` of `Pullback p g` the homotopy fibre of
`Work.StemsB.pullbackFst p g : Pullback p g → E` at `y` has trivial `π_k` for `k ≤ N - 1`. -/
theorem subsingleton_homotopyFibre_pullbackFst {Γ B E : Type} [TopologicalSpace Γ]
    [TopologicalSpace B] [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B))
    (hp : Work.StemsB.IsSerreFibration p) (N : ℕ) (hN : 1 ≤ N)
    (hg : ∀ i : ℕ, i ≤ N → ∀ x : Γ, Function.Bijective (Work.Serre.piMapN g i x)) :
    ∀ y : Work.StemsB.Pullback p g, ∀ k : ℕ, k ≤ N - 1 →
      Subsingleton (HomotopyGroup (Fin k)
        (Work.RatHurewicz.homotopyFibre (Work.StemsB.pullbackFst p g) y)
        (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst p g) y)) := by
  intro y k hk
  have hsub := Work.Serre.subsingleton_homotopyFibre_of_piMapN g N hN
    (Work.StemsB.pullbackSnd p g y) hg k hk
  have hb := Work.RatHurewicz.homotopyFibreMap_basepoint (Work.StemsB.pullbackFst p g) g p
    (Work.StemsB.pullbackSnd p g) (pbSquare g p) y
  have hsub' : Subsingleton (HomotopyGroup (Fin k)
      (Work.RatHurewicz.homotopyFibre g (Work.StemsB.pullbackSnd p g y))
      (Work.RatHurewicz.homotopyFibreMap (Work.StemsB.pullbackFst p g) g p
        (Work.StemsB.pullbackSnd p g) (pbSquare g p) y
        (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst p g) y))) := by
    rw [hb]
    exact hsub
  refine ⟨fun a b => ?_⟩
  have key : ∀ γ : GenLoop (Fin k) (Work.RatHurewicz.homotopyFibre (Work.StemsB.pullbackFst p g) y)
      (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst p g) y),
      GenLoop.Homotopic γ GenLoop.const := by
    intro γ
    have h1 : (⟦Work.StemsB.genLoopMap (Work.RatHurewicz.homotopyFibreMap
        (Work.StemsB.pullbackFst p g) g p (Work.StemsB.pullbackSnd p g) (pbSquare g p) y) k γ⟧
        : HomotopyGroup (Fin k) (Work.RatHurewicz.homotopyFibre g (Work.StemsB.pullbackSnd p g y))
          (Work.RatHurewicz.homotopyFibreMap (Work.StemsB.pullbackFst p g) g p
            (Work.StemsB.pullbackSnd p g) (pbSquare g p) y
            (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst p g) y)))
        = ⟦GenLoop.const⟧ := hsub'.elim _ _
    exact Work.Serre.homotopyFibreMap_lift_nullhomotopy p g hp (pbSquare g p) y k γ
      (Quotient.exact h1)
  refine Quotient.inductionOn a (fun γ => ?_)
  refine Quotient.inductionOn b (fun δ => ?_)
  exact Quotient.sound ((key γ).trans (key δ).symm)

/-! ## The `π₀` case -/

theorem joined_of_genLoopZero_homotopic {X : Type} [TopologicalSpace X] {x p q : X}
    (h : GenLoop.Homotopic (Work.Serre.genLoopZero X x p) (Work.Serre.genLoopZero X x q)) :
    Joined p q := by
  obtain ⟨H⟩ := h
  exact ⟨Path.mk ⟨fun t => H (t, fun _ => 0),
    H.continuous.comp (continuous_id.prodMk continuous_const)⟩
    (H.map_zero_left (fun _ => 0)) (H.map_one_left (fun _ => 0))⟩

theorem genLoopZero_eq_iff {X : Type} [TopologicalSpace X] {x p q : X} :
    ((⟦Work.Serre.genLoopZero X x p⟧ : HomotopyGroup (Fin 0) X x)
        = ⟦Work.Serre.genLoopZero X x q⟧) ↔ Joined p q :=
  ⟨fun h => joined_of_genLoopZero_homotopic (Quotient.exact h),
    fun h => Quotient.sound (Work.Serre.genLoopZero_homotopic h.some)⟩

theorem eq_genLoopZero {X : Type} [TopologicalSpace X] {x : X} (γ : Ω^ (Fin 0) X x) :
    γ = Work.Serre.genLoopZero X x (γ (fun _ => 0)) := by
  apply GenLoop.ext
  intro u
  show γ u = γ (fun _ => 0)
  exact congrArg γ (Subsingleton.elim u (fun _ => 0))

theorem joined_of_joined_image {A W : Type} [TopologicalSpace A] [TopologicalSpace W]
    (i : C(A, W)) (b b' : A)
    (h : Subsingleton (HomotopyGroup (Fin 0) (Work.RatHurewicz.homotopyFibre i b)
      (Work.RatHurewicz.homotopyFibreBasepoint i b)))
    (hb : Joined (i b) (i b')) : Joined b b' := by
  obtain ⟨γ⟩ := hb
  have hjoin : Joined (Work.RatHurewicz.homotopyFibreBasepoint i b)
      (⟨(b', ⟨γ.toContinuousMap, γ.source'⟩), γ.target'⟩ :
        Work.RatHurewicz.homotopyFibre i b) :=
    (genLoopZero_eq_iff (x := Work.RatHurewicz.homotopyFibreBasepoint i b)).mp
      (h.elim _ _)
  have hmap : Joined ((Work.RatHurewicz.homotopyFibreFst i b)
        (Work.RatHurewicz.homotopyFibreBasepoint i b))
      ((Work.RatHurewicz.homotopyFibreFst i b)
        (⟨(b', ⟨γ.toContinuousMap, γ.source'⟩), γ.target'⟩ :
          Work.RatHurewicz.homotopyFibre i b)) :=
    hjoin.map (Work.RatHurewicz.homotopyFibreFst i b).continuous
  exact hmap

theorem piMapN_zero_injective {A W : Type} [TopologicalSpace A] [TopologicalSpace W]
    (i : C(A, W)) (a : A)
    (h : ∀ b : A, Subsingleton (HomotopyGroup (Fin 0) (Work.RatHurewicz.homotopyFibre i b)
      (Work.RatHurewicz.homotopyFibreBasepoint i b))) :
    Function.Injective (Work.Serre.piMapN i 0 a) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h γ =>
    induction y using Quotient.inductionOn with
    | h γ' =>
      obtain ⟨p⟩ : Joined (i (γ (fun _ => 0))) (i (γ' (fun _ => 0))) := by
        have h2 : (⟦Work.Serre.genLoopZero W (i a) (i (γ (fun _ => 0)))⟧
            : HomotopyGroup (Fin 0) W (i a))
            = ⟦Work.Serre.genLoopZero W (i a) (i (γ' (fun _ => 0)))⟧ := by
          have h3 := hxy
          rw [show (⟦γ⟧ : HomotopyGroup (Fin 0) A a)
                = ⟦Work.Serre.genLoopZero A a (γ (fun _ => 0))⟧ from
                congrArg _ (eq_genLoopZero γ),
            show (⟦γ'⟧ : HomotopyGroup (Fin 0) A a)
                = ⟦Work.Serre.genLoopZero A a (γ' (fun _ => 0))⟧ from
                congrArg _ (eq_genLoopZero γ'),
            Work.Serre.piMapN_zero_genLoopZero, Work.Serre.piMapN_zero_genLoopZero] at h3
          exact h3
        exact genLoopZero_eq_iff.mp h2
      obtain ⟨p'⟩ : Joined (γ (fun _ => 0)) (γ' (fun _ => 0)) :=
        joined_of_joined_image i _ _ (h _) ⟨p⟩
      apply Quotient.sound
      rw [eq_genLoopZero γ, eq_genLoopZero γ']
      exact Work.Serre.genLoopZero_homotopic p'

theorem piMapN_zero_surjective {A W : Type} [TopologicalSpace A] [TopologicalSpace W]
    (i : C(A, W)) (a : A)
    (hconn : ∀ w : W, ∃ a' : A, Nonempty (Path w (i a'))) :
    Function.Surjective (Work.Serre.piMapN i 0 a) := by
  intro z
  induction z using Quotient.inductionOn with
  | h γ =>
    obtain ⟨a', ha'⟩ := hconn (γ (fun _ => 0))
    refine ⟨⟦Work.Serre.genLoopZero A a a'⟧, ?_⟩
    rw [Work.Serre.piMapN_zero_genLoopZero, eq_genLoopZero γ]
    apply Quotient.sound
    exact Work.Serre.genLoopZero_homotopic ha'.some.symm

/-- **The `π₀` case of the base change.**  If every point of `W` is joined to a point of the image
of `i`, and the homotopy fibre of `i` has trivial `π₀` over every point, then `i` is bijective on
`π₀`. -/
theorem piZeroBijective_of_hconn0_of_relPiZero {X W : Type} [TopologicalSpace X]
    [TopologicalSpace W] (i : C(X, W)) (x₀ : X)
    (hconn0 : ∀ w : W, ∃ x : X, Nonempty (Path w (i x)))
    (hsub : ∀ b : X, Subsingleton (Work.RatHurewicz.RelHomotopyGroup i b 0)) :
    Function.Bijective (Work.Serre.piMapN i 0 x₀) :=
  ⟨piMapN_zero_injective i x₀ hsub, piMapN_zero_surjective i x₀ hconn0⟩

/-! ## The connectivity of `pullbackSnd` -/

/-- **Base change of a `π`-isomorphism along a Serre fibration.**  If `p : E → B` is a Serre
fibration and `g : Γ → B` is bijective on `π_i` for all `i ≤ N` (`N ≥ 1`), then
`pullbackSnd g p : Γ ×_B E → E` is bijective on `π_i` for all `i < N`. -/
theorem piMapN_pullbackSnd_bijective {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ)
    (hp : Work.StemsB.IsSerreFibration p) (N : ℕ) (hN : 1 ≤ N)
    (hg : ∀ i : ℕ, i ≤ N → ∀ x : Γ, Function.Bijective (Work.Serre.piMapN g i x)) :
    ∀ i : ℕ, i < N → ∀ x : Work.StemsB.Pullback g p,
      Function.Bijective (Work.Serre.piMapN (Work.StemsB.pullbackSnd g p) i x) := by
  intro i hi x
  refine bijective_piMapN_pullbackSnd_of_fst g p i x ?_
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    exact piZeroBijective_of_hconn0_of_relPiZero (Work.StemsB.pullbackFst p g) (pbSwap g p x)
      (Work.Serre.exists_path_pullbackFst p g hp N γ₀ hg)
      (fun b => subsingleton_homotopyFibre_pullbackFst g p hp N hN hg b 0 (by omega))
  · have hN2 : 2 ≤ N := by omega
    refine Work.Serre.rwPiBijectiveOfRelPiVanishing (N - 2) (Work.StemsB.pullbackFst p g)
      (Work.Serre.exists_path_pullbackFst p g hp N γ₀ hg)
      (fun b k hk => subsingleton_homotopyFibre_pullbackFst g p hp N hN hg b k (by omega))
      (fun b y => ?_) i (by omega) (pbSwap g p x)
    haveI : Subsingleton (Work.RatHurewicz.RelHomotopyGroup (Work.StemsB.pullbackFst p g) b
        ((N - 2) + 1)) :=
      subsingleton_homotopyFibre_pullbackFst g p hp N hN hg b ((N - 2) + 1) (by omega)
    have h2 : Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst (Work.StemsB.pullbackFst p g) b)
        (N - 2) (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst p g) b) y = 1 := by
      rw [Subsingleton.elim y 1, map_one]
    exact h2

end

end Work.Serre.SPC
