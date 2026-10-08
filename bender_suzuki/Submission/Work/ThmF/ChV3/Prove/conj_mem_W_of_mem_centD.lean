import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Prove.V_conj_X5
import Submission.Work.ThmF.ChV12.prop3_frobenius_power

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.conj_mem_W_of_mem_centD` — `V = C_D(t)` normalises `W = C_V(K)`

Peterfalvi II, Ch. V §3 (the standing group-theoretic fact behind step (1), `V = W ⋊ P`).

With `D = twoPoint H t = H ∩ H^t`, `V = centD H t = C_D(t)`, `K = Kset H t = J(D,t)` and
`W = W H t = C_V(K)`, every `v ∈ V` normalises `W`.

Both defining pieces of `W = V ∩ C_G(K)` are preserved by conjugation with `v ∈ V`:

* `v ∈ V` means `v ∈ H`, `v ∈ H^t` and `t v = v t`.  Then `v H v⁻¹ = H` (as `v ∈ H`) and
  `v H^t v⁻¹ = H^t` (as `v t v⁻¹ = t`), so `v D v⁻¹ = D`; and `v t v⁻¹ = t` gives
  `v C_G(t) v⁻¹ = C_G(t)`.  So `v V v⁻¹ = V`.  Formally, membership in `D = H ⊓ H^t` and in
  `C_G(t)` is closed under `x ↦ v x v⁻¹` whenever `w ∈ D` (resp. `C_G(t)`), because `H`, `H^t`
  and `C_G(t)` are subgroups containing `v` and `v⁻¹`.
* `v C_G(K) v⁻¹ = C_G(K)`: `w` commutes with `K`, and `v⁻¹ k v ∈ K` for every `k ∈ K` because
  `v⁻¹ ∈ H` with `t v⁻¹ = v⁻¹ t` and `K = J(D,t)` is preserved by such a conjugation
  (`cj_mem_Kset`).  Hence `v w v⁻¹` commutes with every `k ∈ K`.

The standing hypothesis `IsSplitRankOne` is not needed: the statement only uses the definitions
of `centD`, `Kset` and `W`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3.Prove

open Work.ThmF

theorem conj_mem_W_of_mem_centD {G : Type} [Group G] {H : Subgroup G} {t : G} {v w : G}
    (hv : v ∈ Submission.Blueprint.centD H t) (hw : w ∈ Work.ThmF.W H t) :
    v * w * v⁻¹ ∈ Work.ThmF.W H t := by
  -- Unpack `v ∈ V = D ∩ C_G(t)` with `D = H ∩ H^t`.
  obtain ⟨hvD, hvc⟩ := Subgroup.mem_inf.mp hv
  obtain ⟨hvH, hvcH⟩ := Subgroup.mem_inf.mp hvD
  have htv : t * v = v * t := Subgroup.mem_centralizer_iff.mp hvc t (Set.mem_singleton t)
  -- Unpack `w ∈ W = V ∩ C_G(K)`.
  obtain ⟨hwD, hwK⟩ := Subgroup.mem_inf.mp hw
  obtain ⟨hwV, hwc⟩ := Subgroup.mem_inf.mp hwD
  obtain ⟨hwH, hwcH⟩ := Subgroup.mem_inf.mp hwV
  have htw : t * w = w * t := Subgroup.mem_centralizer_iff.mp hwc t (Set.mem_singleton t)
  -- `t` commutes with `v⁻¹` as well (conjugation by `t` fixes `v`, hence also `v⁻¹`).
  have hvt_inv : t * v⁻¹ = v⁻¹ * t := by
    have key : v * t * v⁻¹ = t := by rw [← htv]; group
    calc t * v⁻¹ = v⁻¹ * (v * t * v⁻¹) := by group
      _ = v⁻¹ * t := by rw [key]
  rw [Work.ThmF.le_W_iff]
  refine ⟨?_, ?_⟩
  · -- `v * w * v⁻¹ ∈ V = D ∩ C_G(t)`
    rw [Submission.Blueprint.centD, Subgroup.mem_inf, Submission.Blueprint.twoPoint,
      Subgroup.mem_inf]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · -- `∈ H`: `v, w ∈ H`
      exact H.mul_mem (H.mul_mem hvH hwH) (H.inv_mem hvH)
    · -- `∈ H^t`: `H^t` is a subgroup containing `v`, `w` and `v⁻¹`
      exact (Submission.Blueprint.conj t H).mul_mem
        ((Submission.Blueprint.conj t H).mul_mem hvcH hwcH)
        ((Submission.Blueprint.conj t H).inv_mem hvcH)
    · -- `∈ C_G(t)`: `t` commutes with `v`, `w` and `v⁻¹`
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      calc t * (v * w * v⁻¹) = (t * v) * w * v⁻¹ := by group
        _ = (v * t) * w * v⁻¹ := by rw [htv]
        _ = v * (t * w) * v⁻¹ := by group
        _ = v * (w * t) * v⁻¹ := by rw [htw]
        _ = v * w * (t * v⁻¹) := by group
        _ = v * w * (v⁻¹ * t) := by rw [hvt_inv]
        _ = (v * w * v⁻¹) * t := by group
  · -- `v * w * v⁻¹ ∈ C_G(K)`: `w` commutes with `K` and `v⁻¹ K v ⊆ K`
    intro k hk
    have hk' : v⁻¹ * k * v ∈ Kset H t := by
      simpa using
        cj_mem_Kset (H := H) (t := t) (v := v⁻¹) (x := k) (H.inv_mem hvH) hvt_inv hk
    have hcomm : (v⁻¹ * k * v) * w = w * (v⁻¹ * k * v) :=
      Subgroup.mem_centralizer_iff.mp hwK (v⁻¹ * k * v) hk'
    calc k * (v * w * v⁻¹) = v * ((v⁻¹ * k * v) * w) * v⁻¹ := by group
      _ = v * (w * (v⁻¹ * k * v)) * v⁻¹ := by rw [hcomm]
      _ = (v * w * v⁻¹) * k := by group

end Work.ThmF.ChV3.Prove
