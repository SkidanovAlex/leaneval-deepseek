import Mathlib
import Submission.Work.RatHurewicz.CompressionDefs
import Submission.Work.RatHurewicz.CompressionGeometry
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.RelPiPathDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A pinched map of pairs is null-homotopic when the relative group vanishes

`Work.RatHurewicz.pinchedMap_nullHomotopic`: if `Φ : (I^{e+1}, ∂I^{e+1}) → (Y,A)` is a map of pairs
which is pinched at `a ∈ A` (`IsPinchedAt e Φ a`: constant `a` on the bottom face and on the side
faces) and the `e`-th homotopy group of the homotopy fibre of `A ↪ Y` at `a` is trivial, then `Φ` is
homotopic to the constant map at `a` *through maps of pairs*.

The proof unwraps `Φ` to a based `e`-cube in the homotopy fibre: `q u := (Φ (·,1), s ↦ Φ (·,s))`,
which is a point of the fibre because the paths start at `a` (bottom face) and end in `A` (top
face), and the side faces make `q` based.  The triviality of the homotopy group makes `q` homotopic
to the constant cube *relative to the boundary*, and evaluating the resulting family of fibre
points at the last coordinate gives the required homotopy.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Topology unitInterval Topology.Homotopy
open Work.StemsB (PathSpace evalOne)

namespace Work.RatHurewicz

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {A : Set Y}

/-- The map `(u, s) ↦ Fin.snoc u s` is continuous. -/
theorem continuous_snocTuple (e : ℕ) :
    Continuous fun p : ICube e × unitInterval => (Fin.snoc p.1 p.2 : ICube (e + 1)) := by
  refine continuous_pi fun i => ?_
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp only [Fin.snoc_castSucc]
    exact (continuous_apply j).comp continuous_fst
  · simp only [Fin.snoc_last]
    exact continuous_snd

/-- Reassembling a cube from its first `e` coordinates and its last coordinate. -/
theorem snoc_init_self' {e : ℕ} (x : ICube (e + 1)) :
    Fin.snoc (Fin.init x) (x (Fin.last e)) = x :=
  Fin.snoc_init_self (q := x)

/-- **The based cube in the homotopy fibre associated with a map pinched at `a`.**  A map
`Φ : I^{e+1} → Y` which is constant `a` on the bottom face and maps the top face into `A` gives a
map `u ↦ (Φ (·,1), s ↦ Φ (·,s))` into the homotopy fibre of `A ↪ Y` at `a`. -/
def pinchCube (e : ℕ) (a : ↥A) (Φ : C(ICube (e + 1), Y))
    (hf : ∀ x, x ∈ Cube.boundary (Fin (e + 1)) → Φ x ∈ A)
    (hbot : ∀ u : ICube e, Φ (Fin.snoc u 0) = (a : Y)) :
    C(ICube e, homotopyFibre (setIncl A) a) where
  toFun u :=
    ⟨(⟨Φ (Fin.snoc u 1), hf _ ⟨Fin.last e, Or.inr (Fin.snoc_last ..)⟩⟩,
      (⟨⟨fun s : unitInterval => Φ (Fin.snoc u s), by fun_prop⟩, hbot u⟩ :
        PathSpace Y (setIncl A a))),
      by
        show Φ (Fin.snoc u 1) = Φ (Fin.snoc u 1)
        rfl⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.prodMk ?_ ?_
    · exact Continuous.subtype_mk (Φ.continuous.comp (continuous_snocOne e)) _
    · refine Continuous.subtype_mk ?_ _
      exact ContinuousMap.continuous_of_continuous_uncurry _
        (Φ.continuous.comp (continuous_snocTuple e))

/-- The path of `pinchCube` evaluated at the last coordinate. -/
theorem pinchCube_apply_path {e : ℕ} {a : ↥A} {Φ : C(ICube (e + 1), Y)}
    {hf : ∀ x, x ∈ Cube.boundary (Fin (e + 1)) → Φ x ∈ A}
    {hbot : ∀ u : ICube e, Φ (Fin.snoc u 0) = (a : Y)}
    (u : ICube e) (s : unitInterval) :
    (pinchCube e a Φ hf hbot u).1.2.1 s = Φ (Fin.snoc u s) := rfl

/-- The first coordinate of `pinchCube` is the value of `Φ` on the top face. -/
theorem pinchCube_apply_fst {e : ℕ} {a : ↥A} {Φ : C(ICube (e + 1), Y)}
    {hf : ∀ x, x ∈ Cube.boundary (Fin (e + 1)) → Φ x ∈ A}
    {hbot : ∀ u : ICube e, Φ (Fin.snoc u 0) = (a : Y)}
    (u : ICube e) :
    ((pinchCube e a Φ hf hbot u).1.1 : Y) = Φ (Fin.snoc u 1) := rfl

/-- The cube `pinchCube` is *based* when `Φ` is constant `a` on the side faces as well. -/
theorem pinchCube_base (e : ℕ) (a : ↥A) (Φ : C(ICube (e + 1), Y))
    (hf : ∀ x, x ∈ Cube.boundary (Fin (e + 1)) → Φ x ∈ A)
    (hbot : ∀ u : ICube e, Φ (Fin.snoc u 0) = (a : Y))
    (hside : ∀ (u : ICube e) (s : unitInterval), (∃ i : Fin e, u i = 0 ∨ u i = 1) →
      Φ (Fin.snoc u s) = (a : Y))
    (u : ICube e) (hu : ∃ i : Fin e, u i = 0 ∨ u i = 1) :
    pinchCube e a Φ hf hbot u = homotopyFibreBasepoint (setIncl A) a := by
  refine Subtype.ext (Prod.ext (Subtype.ext (hside u 1 hu)) (Subtype.ext ?_))
  exact ContinuousMap.ext fun s => hside u s hu

/-- **A pinched map of pairs is null-homotopic when the relative group vanishes.** -/
theorem pinchedMap_nullHomotopic (e : ℕ) (a : ↥A)
    (hvan : Subsingleton (RelHomotopyGroup (setIncl A) a e))
    (Φ : C(ICube (e + 1), Y)) (hpin : IsPinchedAt e Φ (a : Y))
    (hA : ∀ x, x ∈ Cube.boundary (Fin (e + 1)) → Φ x ∈ A) :
    ∃ L : C(ICube (e + 1) × unitInterval, Y), (∀ x, L (x, 0) = Φ x) ∧
      (∀ x, x ∈ Cube.boundary (Fin (e + 1)) → ∀ τ : unitInterval, L (x, τ) ∈ A) ∧
      (∀ x, L (x, 1) = (a : Y)) := by
  classical
  have qbase : ∀ u ∈ Cube.boundary (Fin e),
      pinchCube e a Φ hA hpin.1 u = homotopyFibreBasepoint (setIncl A) a :=
    fun u hu => pinchCube_base e a Φ hA hpin.1 hpin.2 u hu
  let q : Ω^ (Fin e) (homotopyFibre (setIncl A) a) (homotopyFibreBasepoint (setIncl A) a) :=
    ⟨pinchCube e a Φ hA hpin.1, qbase⟩
  have hpp : (⟦q⟧ : RelHomotopyGroup (setIncl A) a e)
      = ⟦(GenLoop.const : Ω^ (Fin e) (homotopyFibre (setIncl A) a)
          (homotopyFibreBasepoint (setIncl A) a))⟧ :=
    @Subsingleton.elim (RelHomotopyGroup (setIncl A) a e) hvan _ _
  have hHp : GenLoop.Homotopic q (GenLoop.const :
      Ω^ (Fin e) (homotopyFibre (setIncl A) a) (homotopyFibreBasepoint (setIncl A) a)) :=
    Quotient.exact hpp
  obtain ⟨Hp⟩ := hHp
  have hHp0 : ∀ u : ICube e, Hp ((0 : unitInterval), u) = pinchCube e a Φ hA hpin.1 u :=
    fun u => Hp.map_zero_left u
  have hHp1 : ∀ u : ICube e, Hp ((1 : unitInterval), u)
      = homotopyFibreBasepoint (setIncl A) a :=
    fun u => Hp.map_one_left u
  have hHpbd : ∀ (τ : unitInterval) (u : ICube e), u ∈ Cube.boundary (Fin e) →
      Hp (τ, u) = pinchCube e a Φ hA hpin.1 u := fun τ u hu => Hp.eq_fst τ hu
  have Lcont : Continuous (fun p : ICube (e + 1) × unitInterval =>
      (Hp (p.2, Fin.init p.1)).1.2.1 (p.1 (Fin.last e))) := by
    have h1 : Continuous fun p : ICube (e + 1) × unitInterval => Hp (p.2, Fin.init p.1) :=
      Hp.continuous.comp (Continuous.prodMk continuous_snd
        ((continuous_init e).comp continuous_fst))
    have h2 : Continuous fun p : ICube (e + 1) × unitInterval =>
        (Hp (p.2, Fin.init p.1)).1.2.1 :=
      (fibreCMFamily a).continuous.comp h1
    exact continuous_eval.comp (h2.prodMk
      ((continuous_apply (Fin.last e)).comp continuous_fst))
  refine ⟨⟨fun p => (Hp (p.2, Fin.init p.1)).1.2.1 (p.1 (Fin.last e)), Lcont⟩, ?_, ?_, ?_⟩
  · intro x
    show (Hp ((0 : unitInterval), Fin.init x)).1.2.1 (x (Fin.last e)) = Φ x
    rw [hHp0 (Fin.init x), pinchCube_apply_path, snoc_init_self' x]
  · intro x hx τ
    show (Hp (τ, Fin.init x)).1.2.1 (x (Fin.last e)) ∈ A
    rcases hx with ⟨i, hi | hi⟩
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · have hu : Fin.init x ∈ Cube.boundary (Fin e) := ⟨j, Or.inl hi⟩
        rw [hHpbd τ (Fin.init x) hu, pinchCube_apply_path, snoc_init_self' x]
        exact hA x ⟨_, Or.inl hi⟩
      · rw [show x (Fin.last e) = (0 : unitInterval) from hi]
        show fibreCM (Hp (τ, Fin.init x)) 0 ∈ A
        rw [fibreCM_zero (Hp (τ, Fin.init x))]
        exact a.2
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · have hu : Fin.init x ∈ Cube.boundary (Fin e) := ⟨j, Or.inr hi⟩
        rw [hHpbd τ (Fin.init x) hu, pinchCube_apply_path, snoc_init_self' x]
        exact hA x ⟨_, Or.inr hi⟩
      · rw [show x (Fin.last e) = (1 : unitInterval) from hi]
        show fibreCM (Hp (τ, Fin.init x)) 1 ∈ A
        rw [fibreCM_one (Hp (τ, Fin.init x))]
        exact (Hp (τ, Fin.init x)).1.1.2
  · intro x
    show (Hp ((1 : unitInterval), Fin.init x)).1.2.1 (x (Fin.last e)) = (a : Y)
    rw [hHp1 (Fin.init x)]
    rfl

end

end Work.RatHurewicz
