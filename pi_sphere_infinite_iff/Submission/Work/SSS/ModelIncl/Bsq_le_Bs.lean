import Mathlib
import Submission.Work.SSS.FibreColDefs

namespace Work.SSS.ModelIncl

open CategoryTheory CategoryTheory.Limits

attribute [-instance] AddCommGroup.toIntModule

noncomputable section

/-! ## Functoriality of the transition maps `Finc` and their interaction with the differentials

`Finc ξ s' s h n : (F_{s'})_n → (F_s)_n` is the `n`-th component of the chain map
`F_{s'} → F_s` induced by the filtration.  The three lemmas below are the only structural facts
about it that the comparison of the models `B² ⊆ B^s` needs:

* `Finc_eq_of_le` : proof irrelevance in the comparison `s' ≤ s`;
* `dFs_Finc` : `Finc` commutes with the differentials (naturality of the chain map);
* `Finc_comp` : `Finc` is compatible with composition of comparisons. -/

private lemma Finc_eq_of_le {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) {s' s : ℕ}
    (h₁ h₂ : s' ≤ s) (n : ℕ) : Finc ξ s' s h₁ n = Finc ξ s' s h₂ n := by
  simp only [Finc]

private lemma dFs_Finc {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) {s' s : ℕ}
    (h : s' ≤ s) (a b : ℕ) (x : (ξ.F.obj s').X a) :
    dFs ξ s a b (Finc ξ s' s h a x) = Finc ξ s' s h b (dFs ξ s' a b x) :=
  congrArg (fun (φ : (ξ.F.obj s').X a ⟶ (ξ.F.obj s).X b) => φ.hom x)
    (HomologicalComplex.Hom.comm (ξ.F.map (homOfLE h)) a b)

private lemma Finc_comp {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (n : ℕ) (x : (ξ.F.obj a).X n) :
    Finc ξ a c (le_trans hab hbc) n x = Finc ξ b c hbc n (Finc ξ a b hab n x) := by
  have hmap : ξ.F.map (homOfLE (le_trans hab hbc))
      = ξ.F.map (homOfLE hab) ≫ ξ.F.map (homOfLE hbc) := by
    rw [← Functor.map_comp]
    congr 1
  exact congrArg (fun (φ : ξ.F.obj a ⟶ ξ.F.obj c) => (φ.f n).hom x) hmap

/-- `Bstep ξ s t h n` is the general model of the boundary submodule at `t`: the image in
`(F_s/F_{s-1})_n` of the `y ∈ (F_s)_n` for which `∂(F_t)_{n+1}` contains the image of `y`.  The
models used in the transgression are `Bsq ξ s n = Bstep ξ s (s+1) _ n` (boundaries coming from
`F_{s+1}`) and `Bs ξ s n = Bstep ξ s (2*s-1) _ n` (boundaries coming from `F_{2s-1}`). -/
private def Bstep {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C)
    (s t : ℕ) (h : s ≤ t) (n : ℕ) : Submodule ℤ ((grF ξ.F s).X n) :=
  Submodule.map (projQ ξ s n)
    (Submodule.comap (Finc ξ s t h n)
      (Submodule.map (dFs ξ t (n + 1) n)
        (Submodule.comap (dFs ξ t (n + 1) n) (LinearMap.range (Finc ξ s t h n)))))

/-- `Bstep` is monotone in the filtration index `t`: enlarging the chain group out of which the
boundaries are taken can only produce more boundary classes. -/
private lemma Bstep_mono {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) (s n : ℕ)
    {t t' : ℕ} (h : s ≤ t) (htt' : t ≤ t') :
    Bstep ξ s t h n ≤ Bstep ξ s t' (le_trans h htt') n := by
  rw [Bstep, Bstep]
  apply Submodule.map_mono
  intro y hy
  rw [Submodule.mem_comap] at hy ⊢
  obtain ⟨e, -, heq⟩ := Submodule.mem_map.mp hy
  have key : dFs ξ t' (n + 1) n (Finc ξ t t' htt' (n + 1) e)
      = Finc ξ s t' (le_trans h htt') n y := by
    rw [dFs_Finc ξ htt' (n + 1) n e, heq, ← Finc_comp ξ h htt' n y]
  refine ⟨Finc ξ t t' htt' (n + 1) e, ?_, key⟩
  show dFs ξ t' (n + 1) n (Finc ξ t t' htt' (n + 1) e)
      ∈ (Finc ξ s t' (le_trans h htt') n).range
  exact ⟨y, key.symm⟩

/-- Inside the chains `(F_s/F_{s-1})_n` of the graded piece, `B²_{s,n} ⊆ B^s_{s,n}`: boundaries
coming from `F_{s+1}` are among those coming from `F_{2s-1}` (using `F_{s+1} ⊆ F_{2s-1}`, which is
why `2 ≤ s` is assumed). -/
theorem Bsq_le_Bs {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) (s n : ℕ) (hs : 2 ≤ s) :
    Bsq ξ s n ≤ Bs ξ s n := by
  have h1 : s + 1 ≤ 2 * s - 1 := by omega
  have h2 : s ≤ 2 * s - 1 := le_trans (Nat.le_succ s) h1
  have hmono := Bstep_mono ξ s n (Nat.le_succ s) h1
  have e₁ : Bsq ξ s n = Bstep ξ s (s + 1) (Nat.le_succ s) n := by simp only [Bsq, Bstep]
  have e₂ : Bs ξ s n = Bstep ξ s (2 * s - 1) h2 n := by simp only [Bs, Bstep]
  rw [e₁, e₂]
  exact hmono

end

end Work.SSS.ModelIncl
