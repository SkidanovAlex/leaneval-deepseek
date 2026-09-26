import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.ZMultiples

noncomputable section

open scoped Topology
open AddSubgroup

namespace Commons.Topology.AddCircle

/-- A `T`-periodic continuous map `f : ℝ → AddCircle p` admits a continuous lift
`G : ℝ → ℝ`, and translation by the period `T` acts on the lift by adding a fixed
integer multiple of `p` (the "advance"/degree of the induced circle map). -/
theorem circleMap_lift_advance (T p : ℝ) (hp : p ≠ 0) {f : ℝ → AddCircle p}
    (hf : Continuous f) (hper : ∀ t : ℝ, f (t + T) = f t) :
    ∃ G : ℝ → ℝ, Continuous G ∧ (∀ t : ℝ, (G t : AddCircle p) = f t) ∧
      ∃ k : ℤ, ∀ t : ℝ, G (t + T) = G t + (k : ℝ) * p := by
  have _ : p ≠ 0 := hp
  -- ℝ → AddCircle p is a covering map, so (since ℝ is simply connected) f lifts.
  have hcov : IsCoveringMap (fun x : ℝ => (x : AddCircle p)) := by
    simpa using (AddCircle.isCoveringMap_coe (𝕜 := ℝ) p)
  obtain ⟨e₀, he0⟩ : ∃ e₀ : ℝ, (e₀ : AddCircle p) = f 0 := by
    simpa using (QuotientAddGroup.mk_surjective (s := zmultiples p) (f 0))
  let fC : C(ℝ, AddCircle p) := ⟨f, hf⟩
  obtain ⟨F, hFlift, _hFun⟩ :=
    hcov.existsUnique_continuousMap_lifts fC 0 e₀ (by simpa [fC] using he0)
  let G : ℝ → ℝ := fun t => F t
  have hG_cont : Continuous G := by
    simpa [G] using F.continuous
  have hG_lift : ∀ t : ℝ, (G t : AddCircle p) = f t := by
    intro t
    simpa [G, fC] using (congrFun hFlift.2 t)
  -- The "advance" φ(t) = G(t+T) - G t takes values in the discrete subgroup pℤ.
  let φ : ℝ → ℝ := fun t => G (t + T) - G t
  have hφ_cont : Continuous φ := by
    dsimp [φ, G]
    exact (F.continuous.comp (continuous_id.add continuous_const)).sub F.continuous
  have hφ_mem : ∀ t : ℝ, φ t ∈ zmultiples p := by
    intro t
    rw [AddSubgroup.mem_zmultiples_iff]
    rw [← AddCircle.coe_eq_zero_iff (p := p)]
    dsimp [φ, G]
    rw [sub_eq_zero]
    calc
      (F (t + T) : AddCircle p) = f (t + T) := by simpa using hG_lift (t + T)
      _ = f t := hper t
      _ = (F t : AddCircle p) := by simpa using (hG_lift t).symm
  -- Continuous + discrete-valued ⇒ constant on the connected real line.
  let ψ : ℝ → AddSubgroup.zmultiples p := fun t => ⟨φ t, hφ_mem t⟩
  have hψ_cont : Continuous ψ := Continuous.subtype_mk (f := φ) hφ_cont hφ_mem
  have hφ_const : ∀ t : ℝ, φ t = φ 0 := by
    intro t
    have hψc : ψ t = ψ 0 :=
      PreconnectedSpace.constant (α := ℝ) (Y := AddSubgroup.zmultiples p)
        (inferInstance : PreconnectedSpace ℝ) hψ_cont
    exact congrArg Subtype.val hψc
  have hφ0_mem : φ 0 ∈ zmultiples p := hφ_mem 0
  rcases (AddSubgroup.mem_zmultiples_iff.mp hφ0_mem) with ⟨k, hk⟩
  have hk0 : φ 0 = (k : ℝ) * p := hk.symm.trans (zsmul_eq_mul p k)
  refine ⟨G, hG_cont, hG_lift, k, ?_⟩
  intro t
  calc
    G (t + T) = G t + φ t := by dsimp [φ, G]; ring
    _ = G t + φ 0 := by rw [hφ_const t]
    _ = G t + (k : ℝ) * p := by rw [hk0]

end Commons.Topology.AddCircle