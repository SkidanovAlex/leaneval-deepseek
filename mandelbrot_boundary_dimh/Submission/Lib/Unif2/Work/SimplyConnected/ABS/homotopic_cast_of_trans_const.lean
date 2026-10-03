import Mathlib

/-!
# Casting a presupposed null-homotopy along the endpoint identification

If `h : a = b`, `C : Path a b`, and the loop `C.trans ((Path.cast (Path.refl b) h rfl).symm)` at `a`
is null-homotopic, then the path `C`, read as a loop at `a` by casting its endpoints along `h`,
is null-homotopic as well.

The mathematical content is entirely reparametrisation: after substituting `b = a` the
hypothesis says that the concatenation of `C` with a constant loop is null-homotopic, and the
loop `C` itself differs from that concatenation only by inserting a constant tail, which
`Path.Homotopic.trans_refl` accounts for.  The cast bookkeeping is handled by the observation
that `Path.Homotopic` only sees the underlying continuous map of a path, so two paths with the
same underlying map are homotopic (lemma `homotopic_of_coe_eq` below).
-/

namespace Work.SimplyConnected.ABS

/-- `Path.Homotopic` only depends on the underlying continuous map: two paths between the same
endpoints which have the same underlying function are homotopic (by the constant homotopy,
since `ContinuousMap.HomotopyRel` only sees the underlying maps). -/
lemma homotopic_of_coe_eq {X : Type*} [TopologicalSpace X] {a b : X} {p q : Path a b}
    (h : ⇑p = ⇑q) : p.Homotopic q := by
  have ht : p.toContinuousMap = q.toContinuousMap := ContinuousMap.ext (fun t => congrFun h t)
  have : Nonempty (ContinuousMap.HomotopyRel p.toContinuousMap q.toContinuousMap {0,1}) := by
    rw [ht]
    exact ⟨ContinuousMap.HomotopyRel.refl _ _⟩
  exact this

theorem homotopic_cast_of_trans_const {X : Type*} [TopologicalSpace X] {a b : X} (h : a = b)
    (C : Path a b)
    (H : Path.Homotopic (C.trans ((Path.cast (Path.refl b) h rfl).symm)) (Path.refl a)) :
    Path.Homotopic (Path.cast C rfl h) (Path.refl a) := by
  cases h
  -- Everything now lives at a single point, and `Path.cast _ rfl rfl` has the same underlying
  -- map as the path it is cast from.
  have hD : (Path.cast (Path.refl a) rfl rfl).Homotopic (Path.refl a) := homotopic_of_coe_eq rfl
  have hCs : C.Homotopic (Path.cast C rfl rfl) := homotopic_of_coe_eq rfl
  -- The cast constant path is homotopic to the constant path, hence so is its reverse.
  have h1 : (Path.refl a).Homotopic (Path.cast (Path.refl a) rfl rfl).symm := by
    have hh := hD.symm₂
    rw [Path.refl_symm] at hh
    exact hh.symm
  -- So `C` is homotopic to `C` concatenated with the cast constant loop, by `trans_refl`.
  have h2 : C.Homotopic (C.trans (Path.cast (Path.refl a) rfl rfl).symm) := by
    have ht := Path.Homotopic.trans_refl C
    have hc := Path.Homotopic.hcomp (Path.Homotopic.refl C) h1
    exact ht.symm.trans hc
  exact hCs.symm.trans (h2.trans H)

end Work.SimplyConnected.ABS
