import Mathlib
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.Serre.Models
import Submission.Work.Serre.Assembly.pullbackFst_serre
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.Serre.rwPiBijectiveOfRelPiVanishing
import Submission.Work.Serre.homotopyFibreMap_lift_nullhomotopy
import Submission.Work.RatHurewicz.homotopyFibreMap_exists
import Submission.Work.Serre.subsingleton_homotopyFibre_of_piMapN
import Submission.Work.Serre.exists_path_pullbackFst
import Submission.Work.Serre.rwPiMapN_bijective_of_homotopyEquiv

namespace Work.Serre.Assembly

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

variable {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B] [TopologicalSpace E]

/-! ## The two pullbacks of `g` and `p` are exchanged by `(γ,e) ↦ (e,γ)` -/

/-- The swap `(γ,e) ↦ (e,γ)`, as a continuous map `Pullback g p → Pullback p g`. -/
def pullbackSwap (g : C(Γ, B)) (p : C(E, B)) :
    C(Work.StemsB.Pullback g p, Work.StemsB.Pullback p g) where
  toFun x := ⟨(x.1.2, x.1.1), x.2.symm⟩
  continuous_toFun :=
    Continuous.subtype_mk ((continuous_snd.comp continuous_subtype_val).prodMk
      (continuous_fst.comp continuous_subtype_val)) (fun x => x.2.symm)

@[simp] theorem pullbackSwap_apply_fst (g : C(Γ, B)) (p : C(E, B))
    (x : Work.StemsB.Pullback g p) : (pullbackSwap g p x).1.1 = x.1.2 := rfl

@[simp] theorem pullbackSwap_apply_snd (g : C(Γ, B)) (p : C(E, B))
    (x : Work.StemsB.Pullback g p) : (pullbackSwap g p x).1.2 = x.1.1 := rfl

/-- The swap as a homeomorphism. -/
def pullbackSwapHomeomorph (g : C(Γ, B)) (p : C(E, B)) :
    Work.StemsB.Pullback g p ≃ₜ Work.StemsB.Pullback p g where
  toFun := pullbackSwap g p
  invFun := pullbackSwap p g
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  continuous_toFun := (pullbackSwap g p).continuous
  continuous_invFun := (pullbackSwap p g).continuous

/-- `pullbackFst p g ∘ pullbackSwap = pullbackSnd g p`. -/
theorem pullbackFst_comp_pullbackSwap (g : C(Γ, B)) (p : C(E, B)) :
    (Work.StemsB.pullbackFst p g).comp (pullbackSwap g p) = Work.StemsB.pullbackSnd g p := by
  ext x
  rfl

/-! ## The homotopy fibres of the two projections -/

/-- **The swap of homotopy fibres.**  Since `pullbackFst p g ∘ pullbackSwap = pullbackSnd g p`
definitionally on points, the swap acts on the homotopy fibres of the two projections by changing
only the first coordinate. -/
def homotopyFibreSwap (g : C(Γ, B)) (p : C(E, B)) (x : Work.StemsB.Pullback g p) :
    Work.RatHurewicz.homotopyFibre (Work.StemsB.pullbackSnd g p) x ≃ₜ
      Work.RatHurewicz.homotopyFibre (Work.StemsB.pullbackFst p g) (pullbackSwap g p x) where
  toFun y := ⟨(pullbackSwap g p y.1.1, y.1.2), y.2⟩
  invFun y := ⟨(pullbackSwap p g y.1.1, y.1.2), y.2⟩
  left_inv y := by
    refine Subtype.ext ?_
    refine Prod.ext ?_ ?_
    · exact Subtype.ext rfl
    · rfl
  right_inv y := by
    refine Subtype.ext ?_
    refine Prod.ext ?_ ?_
    · exact Subtype.ext rfl
    · rfl
  continuous_toFun :=
    Continuous.subtype_mk (Continuous.prodMk
      ((pullbackSwap g p).continuous.comp (continuous_fst.comp continuous_subtype_val))
      (continuous_snd.comp continuous_subtype_val)) _
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.prodMk
      ((pullbackSwap p g).continuous.comp (continuous_fst.comp continuous_subtype_val))
      (continuous_snd.comp continuous_subtype_val)) _

@[simp] theorem homotopyFibreSwap_fst (g : C(Γ, B)) (p : C(E, B)) (x : Work.StemsB.Pullback g p)
    (y : Work.RatHurewicz.homotopyFibre (Work.StemsB.pullbackSnd g p) x) :
    (homotopyFibreSwap g p x y).1.1 = pullbackSwap g p y.1.1 := rfl

/-! ## The homotopy fibre of the base change -/

/-- **The homotopy fibre of `pullbackFst q g` is trivial wherever the homotopy fibre of `g` is.**
Null-homotopies lift along the comparison map of homotopy fibres of the pullback square
(`Work.Serre.homotopyFibreMap_lift_nullhomotopy`), i.e. that comparison map is injective on every
`π_k`; hence `π_k` of the homotopy fibre of `pullbackFst q g` vanishes as soon as it vanishes for
`g`.  (This is the statement of `Work.Serre.subsingleton_homotopyFibre_of_subsingleton_homotopyFibreMap`
of `Submission/Work/Serre/pullbackFst_piMapN_bijective.lean`, transcribed here so that this file is
self-contained.) -/
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
        Work.Serre.homotopyFibreMap_lift_nullhomotopy q g hq hsq x k γ hV
      have hd : GenLoop.Homotopic δ (GenLoop.const : GenLoop (Fin k)
          (Work.RatHurewicz.homotopyFibre (Work.StemsB.pullbackFst q g) x)
          (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst q g) x)) :=
        Work.Serre.homotopyFibreMap_lift_nullhomotopy q g hq hsq x k δ
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

/-- **Vanishing of the homotopy groups of the fibre of the base change.**  If `p : E → B` is a
Serre fibration and `g : Γ → B` is bijective on `π_i` for every `i ≤ N`, then for every point of
`Pullback p g` the homotopy fibre of `pullbackFst p g : Pullback p g → E` has trivial `π_k` for
`k ≤ N - 1`. -/
theorem subsingleton_homotopyFibre_pullbackFst (g : C(Γ, B)) (p : C(E, B))
    (hp : Work.StemsB.IsSerreFibration p) (N : ℕ) (hN : 1 ≤ N)
    (hg : ∀ i : ℕ, i ≤ N → ∀ x : Γ, Function.Bijective (Work.Serre.piMapN g i x))
    (x : Work.StemsB.Pullback p g) (k : ℕ) (hk : k ≤ N - 1) :
    Subsingleton (HomotopyGroup (Fin k)
      (Work.RatHurewicz.homotopyFibre (Work.StemsB.pullbackFst p g) x)
      (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst p g) x)) :=
  subsingleton_homotopyFibre_of_subsingleton_homotopyFibreMap p g hp x k
    (Work.Serre.subsingleton_homotopyFibre_of_piMapN g N hN (Work.StemsB.pullbackSnd p g x)
      hg k hk)

-- `piMapN (pullbackSnd g p) i` is bijective for `1 ≤ i < N` when `p` is a Serre fibration and
-- `piMapN g i` is bijective for all `i ≤ N`.
--
-- Route 1 (long exact sequences).  `pullbackFst g p : Γ ×_B E → Γ` is a Serre fibration
-- (`Work.Serre.Assembly.pullbackFst_serre`, the base change of `p` along `g`, since
-- `Pullback g p = {(γ,e) // g γ = p e}`), and `p` itself is one.  The fibre of `pullbackFst g p`
-- over `γ` is `{γ} × p⁻¹(g γ)`, canonically homeomorphic to `p⁻¹(g γ)` by the second projection,
-- so the two long exact homotopy sequences (`Work.StemsB.fibrationLES_of_isSerreFibration`) form a
-- ladder along `pullbackSnd g p`, `g` and the fibre homeomorphism; the standard five term exactness
-- argument gives the claim.  At degree `i` one needs the maps on `π_i` and `π_{i+1}` of the base,
-- which is why the hypothesis reaches `N` while the conclusion only reaches `N - 1` (the statement
-- is sharp: `N = 2`, `p = evalOne` on `S²`, `g` the Hopf map gives `π₁(pullbackSnd) : ℤ → 0`).
--
-- Route 2 (homotopy fibres).  The homotopy fibre of `pullbackSnd g p` over a point is weakly
-- equivalent to that of `g` over the corresponding point of `B` (lift along `p` with its HLP);
-- `π_k` of the homotopy fibre of `g` vanishes for `k ≤ N-1` because `g` is bijective on `π_i` for
-- `i ≤ N`; `Work.Serre.rwPiBijectiveOfRelPiVanishing` then gives the claim.
--
-- The proof below runs Route 2 for the map `pullbackFst p g : Pullback p g → E`, which is
-- `pullbackSnd g p` read in the other coordinate order of the fibre product, and then transports
-- the conclusion across the homeomorphism `pullbackSwap g p`.
theorem pullbackSnd_piMapN_bijective {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (N : ℕ)
    (hg : ∀ i : ℕ, i ≤ N → ∀ x : Γ, Function.Bijective (Work.Serre.piMapN g i x)) :
    ∀ i : ℕ, 1 ≤ i → i < N → ∀ x : Work.StemsB.Pullback g p,
      Function.Bijective (Work.Serre.piMapN (Work.StemsB.pullbackSnd g p) i x) := by
  intro i hi1 hiN x
  by_cases hN2 : 2 ≤ N
  · have hN1 : 1 ≤ N := by omega
    -- `π₀`-surjectivity of `pullbackSnd g p`, from that of `pullbackFst p g`
    have hconn0 : ∀ w : E, ∃ a : Work.StemsB.Pullback g p,
        Nonempty (Path w (Work.StemsB.pullbackSnd g p a)) := by
      intro w
      obtain ⟨y, hy⟩ :=
        Work.Serre.exists_path_pullbackFst p g hp N (Work.StemsB.pullbackFst g p x) hg w
      exact ⟨⟨(y.1.2, y.1.1), y.2.symm⟩, hy⟩
    -- the fibre data, transported across the swap of homotopy fibres
    have hvan : ∀ (y : Work.StemsB.Pullback p g) (j : ℕ), j ≤ N - 1 →
        Subsingleton (HomotopyGroup (Fin j)
          (Work.RatHurewicz.homotopyFibre (Work.StemsB.pullbackFst p g) y)
          (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst p g) y)) :=
      fun y j hj => subsingleton_homotopyFibre_pullbackFst g p hp N hN1 hg y j hj
    have hfib : ∀ (a : Work.StemsB.Pullback g p) (j : ℕ), j ≤ N - 1 →
        Subsingleton (HomotopyGroup (Fin j)
          (Work.RatHurewicz.homotopyFibre (Work.StemsB.pullbackSnd g p) a)
          (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackSnd g p) a)) := by
      intro a j hj
      have hbp : (homotopyFibreSwap g p a).toHomotopyEquiv.toFun
            (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackSnd g p) a)
          = Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackFst p g)
              (pullbackSwap g p a) := Subtype.ext rfl
      haveI : Subsingleton (HomotopyGroup (Fin j)
          (Work.RatHurewicz.homotopyFibre (Work.StemsB.pullbackFst p g) (pullbackSwap g p a))
          ((homotopyFibreSwap g p a).toHomotopyEquiv.toFun
            (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackSnd g p) a))) :=
        hbp.symm ▸ hvan (pullbackSwap g p a) j hj
      have hbij : Function.Bijective (Work.Serre.piMapN
          (homotopyFibreSwap g p a).toHomotopyEquiv.toFun j
          (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackSnd g p) a)) :=
        Work.Serre.rwPiMapN_bijective_of_homotopyEquiv (homotopyFibreSwap g p a).toHomotopyEquiv j
          (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackSnd g p) a)
      refine ⟨fun u v => hbij.1 ?_⟩
      exact Subsingleton.elim _ _
    exact Work.Serre.rwPiBijectiveOfRelPiVanishing (N - 2) (Work.StemsB.pullbackSnd g p) hconn0
      (fun a j hj => hfib a j (by omega))
      (fun a z => by
        haveI : Subsingleton (HomotopyGroup (Fin ((N - 2) + 1))
            (Work.RatHurewicz.homotopyFibre (Work.StemsB.pullbackSnd g p) a)
            (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackSnd g p) a)) :=
          hfib a ((N - 2) + 1) (by omega)
        rw [Subsingleton.elim (α := HomotopyGroup (Fin ((N - 2) + 1))
            (Work.RatHurewicz.homotopyFibre (Work.StemsB.pullbackSnd g p) a)
            (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackSnd g p) a)) z 1,
          Work.Serre.piMapN_eq_pimap
            (Work.RatHurewicz.homotopyFibreFst (Work.StemsB.pullbackSnd g p) a) (N - 2)
            (Work.RatHurewicz.homotopyFibreBasepoint (Work.StemsB.pullbackSnd g p) a)]
        exact map_one _)
      i (by omega) x
  · omega

end

end Work.Serre.Assembly
