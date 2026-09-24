import Mathlib.Topology.Homotopy.Lifting

set_option linter.style.haveILetI false

namespace Commons.Topology.Covering

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- **A covering map with trivial monodromy at a point admits a section through it.**

If `p : E → X` is a covering map over a connected, locally path connected base `X`, and every
loop in `X` at `p e₀` lifts to a loop at `e₀` (equivalently, the monodromy representation
`π₁(X, p e₀) → p ⁻¹' {p e₀}` fixes `e₀`), then `p` admits a global continuous section `σ`
with `σ (p e₀) = e₀`.

This is the same statement as `Commons.Topology.Covering.section_of_monodromy_eq_self`, but
without the hypothesis `[LocallyPathConnectedSpace E]` on the total space: that hypothesis is
never used (the lifting theorem of Mathlib, `IsLocalHomeomorph.existsUnique_continuousMap_lifts`,
only requires the *base* to be locally path connected), so the lemma holds in general. -/

private lemma monodromy_mk_liftPath (hp : IsCoveringMap p) {a b : X} (γ : Path a b) (e : E)
    (he : p e = a) :
    (hp.monodromy (Path.Homotopic.Quotient.mk γ) ⟨e, he⟩).1 =
      hp.liftPath γ e (γ.source.trans he.symm) 1 :=
  rfl

theorem section_of_monodromy_eq_self_weak {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [ConnectedSpace X] [LocallyPathConnectedSpace X]
    {p : E → X} (hp : IsCoveringMap p) (e₀ : E)
    (h : ∀ γ : FundamentalGroup X (p e₀), hp.monodromy γ ⟨e₀, rfl⟩ = ⟨e₀, rfl⟩) :
    ∃ σ : C(X, E), σ (p e₀) = e₀ ∧ ∀ x, p (σ x) = x := by
  classical
  haveI : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace
  have huniq : ∀ γ γ' : C(unitInterval, X), ∀ Γ Γ' : C(unitInterval, E),
      γ 0 = p e₀ → γ' 0 = p e₀ → Γ 0 = e₀ → Γ' 0 = e₀ →
        p ∘ Γ = (ContinuousMap.id X).comp γ → p ∘ Γ' = (ContinuousMap.id X).comp γ' →
        γ 1 = γ' 1 → Γ 1 = Γ' 1 := by
    intro γ γ' Γ Γ' hγ0 hγ'0 hΓ0 hΓ'0 hl hl' hγ1
    simp only [ContinuousMap.id_comp] at hl hl'
    let γp : Path (p e₀) (γ 1) := ⟨γ, hγ0, rfl⟩
    let γ'p : Path (p e₀) (γ 1) := ⟨γ', hγ'0, hγ1.symm⟩
    have hlγp : hp.liftPath γp e₀ (γp.source.trans (rfl : p e₀ = p e₀).symm) = Γ :=
      ((hp.eq_liftPath_iff' (γ := γp) (e := e₀)
        (γ_0 := γp.source.trans (rfl : p e₀ = p e₀).symm)).mpr ⟨hl, hΓ0⟩).symm
    have hAval : (hp.monodromy (Path.Homotopic.Quotient.mk γp) ⟨e₀, rfl⟩).1 = Γ 1 := by
      rw [monodromy_mk_liftPath, hlγp]
    have hA : hp.monodromy (Path.Homotopic.Quotient.mk γp) ⟨e₀, rfl⟩ = ⟨Γ 1, congr_fun hl 1⟩ :=
      Subtype.ext hAval
    have hloop := h (Path.Homotopic.Quotient.mk (γp.trans γ'p.symm))
    have htrans : hp.monodromy (Path.Homotopic.Quotient.mk (γp.trans γ'p.symm)) ⟨e₀, rfl⟩
        = hp.monodromy (Path.Homotopic.Quotient.mk γ'p.symm)
            (hp.monodromy (Path.Homotopic.Quotient.mk γp) ⟨e₀, rfl⟩) := by
      rw [Path.Homotopic.Quotient.mk_trans]
      exact hp.monodromy_trans_apply _ _ _
    have eq1 : hp.monodromy (Path.Homotopic.Quotient.mk γ'p.symm) ⟨Γ 1, congr_fun hl 1⟩
        = ⟨e₀, rfl⟩ := by
      have hh := htrans.symm.trans hloop
      rwa [hA] at hh
    let G' : Path e₀ (Γ' 1) := ⟨Γ', hΓ'0, rfl⟩
    have hle : hp.liftPath γ'p.symm (Γ' 1)
        ((γ'p.symm).source.trans ((congr_fun hl' 1).trans hγ1.symm).symm) = G'.symm :=
      ((hp.eq_liftPath_iff' (γ := γ'p.symm) (e := Γ' 1)
        (γ_0 := (γ'p.symm).source.trans ((congr_fun hl' 1).trans hγ1.symm).symm)).mpr
        ⟨by funext t; exact congr_fun hl' _, Path.source G'.symm⟩).symm
    have eq2 : hp.monodromy (Path.Homotopic.Quotient.mk γ'p.symm)
        ⟨Γ' 1, (congr_fun hl' 1).trans hγ1.symm⟩ = ⟨e₀, rfl⟩ := by
      apply Subtype.ext
      rw [monodromy_mk_liftPath, hle]
      exact Path.target G'.symm
    have hinj := (hp.monodromy_bijective (Path.Homotopic.Quotient.mk γ'p.symm)).1
    exact congrArg Subtype.val (hinj (eq1.trans eq2.symm))
  have hex : ∀ γ : C(unitInterval, X), γ 0 = p e₀ →
      ∃ Γ : C(unitInterval, E), Γ 0 = e₀ ∧ p ∘ Γ = (ContinuousMap.id X).comp γ := by
    intro γ hγ0
    obtain ⟨Γ, hΓl, hΓ0⟩ := hp.exists_path_lifts γ e₀ hγ0
    exact ⟨Γ, hΓ0, by simpa using hΓl⟩
  obtain ⟨σ, ⟨hσ0, hσp⟩, -⟩ :=
    (hp.isLocalHomeomorph).existsUnique_continuousMap_lifts (ContinuousMap.id X) (p e₀) e₀ rfl
      hex huniq
  exact ⟨σ, hσ0, fun x => by simpa using congr_fun hσp x⟩

end Commons.Topology.Covering
