import Mathlib
import Submission.Work.ThomBordism.gaussBranch_uniform_full
import Submission.Work.ThomBordism.localDegree_universalThomClass
import Submission.Work.ThomBordism.gtdGaussCandidate

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The branch uniformity of `pulledThom_gauss`, from the universal local-degree class

`Work.ThomBordism.gaussBranch_uniform_full` reduces the uniformity of the Gauss branch (the field
`Work.PTGeometric.GenuineTubeGeometry.pulledThom_gauss`) to the input `hcan`: a **single** sign `t`
such that for every piece the *canonical* (`padGaussFun`-plane, `padEuc`-vector) Gauss candidate is a
local-degree class up to `t`.

Here we *produce* `hcan`, from the universal local-degree class
`Work.ThomBordism.localDegree_universalThomClass`: if `u₀` is a single Thom class of `γ_{k,10}`
whose pullback `gtdUWith … u₀` implements the local degree of every datum, and
`Grassmann.tautologicalThomClass k 10 = s • u₀` (the classes of `γ_{k,10}` are unique up to sign),
then the branch of *every* recorded Gauss datum is the *same* sign `s`:

* the plain candidate `Gp` of the piece's normal data satisfies
  `gtdU (Gp) = s • gtdUWith (Gp) u₀`, so `IsLocalDegreeClass (s • gtdU (Gp))` (universality);
* the recorded candidate `Gc` satisfies `gtdU (Gc) = η • gtdU (Gp)` with `η = ±1` (the flip lemma
  `Work.ThomBordism.gtdU_eq_zsmul_of_branch_aux_le`), and `IsLocalDegreeClass (gtdU (Gc))` by the
  field `GenuineTubeGeometry.localDegree`; the uniqueness
  `Work.ThomBordism.isLocalDegreeClass_zsmul_eq` gives `η * s = 1`, hence `η = s`.

So `hcan` holds with the *global* sign `s`, and `gaussBranch_uniform_full` applies.  Nothing here
needs connectivity: only `Nonempty (Fam i).pt`, which
`Work.PTGeometric.GenuineTubeGeometry.nonempty` supplies.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

open Work.ThomBordism.PontryaginThom Work.Tubular

/-! ## `gtdUWith` depends on the Thom class only through its cochain -/

/-- `gtdUWith` is `ℤ`-linear in the cochain of the Thom class, for unit scalars. -/
theorem gtdUWith_eq_zsmul_of_tau_eq {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (G : C((normalBundle E ND).TotalSpace, (Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10))
    {U U' : Work.Thom.ThomClass (Grassmann.tautologicalBundle k 10) k} {s : ℤ}
    (hs : s = 1 ∨ s = -1) (h : U.τ = s • U'.τ) :
    gtdUWith E ND G hgm U = s • gtdUWith E ND G hgm U' := by
  rcases hs with hs | hs
  · subst hs
    rw [one_smul] at h
    rw [gtdUWith_eq_of_tau_eq E ND G hgm h, one_smul]
  · subst hs
    have hτ : U.τ = (ThomClass.neg U').τ := by
      show U.τ = -U'.τ
      simpa using h
    rw [gtdUWith_eq_of_tau_eq E ND G hgm hτ, gtdUWith_neg]
    simp

/-! ## The plain Gauss candidate at an arbitrary normal datum -/

/-- **The canonical (`padGaussFun`-plane, `padEuc`-vector) Gauss candidate** of an arbitrary normal
datum `ND`, with no hypothesis on the manifold.

This is the `∃ G, …` part of `Work.ThomBordism.gtdGaussCandidate` (whose statement carries
`[ConnectedSpace V.pt]`, used only for the *local-degree* half of that theorem): the construction is
the `Grassmann.tautTotalMap` of the padded Gauss plane and the padded normal coordinate. -/
theorem exists_plainGaussCandidate {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    ∃ (Gp : C((normalBundle E ND).TotalSpace,
        (Grassmann.tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (normalBundle E ND),
        Gp p ∈ Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10)),
      (∀ p, (Grassmann.tautologicalBundle k 10).proj (Gp p)
        = Grassmann.padGaussFun E ND p.1) ∧
      (∀ p, Grassmann.evalVec (Gp p)
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            (NormalTotal.vec (bundleToNormal E ND p))) := by
  classical
  let P : C((normalBundle E ND).TotalSpace, Grassmann.OG k 10) :=
    ⟨fun p => Grassmann.padGaussFun E ND p.1,
      (Grassmann.continuous_padGaussFun E ND).comp
        (Work.TangentClasses.RealBundle.continuous_proj (normalBundle E ND))⟩
  let W : C((normalBundle E ND).TotalSpace, Grassmann.Amb (k + 10)) :=
    ⟨fun p => Work.PTGeometric.padEuc k 10 (by norm_num)
        (NormalTotal.vec (bundleToNormal E ND p)),
      (Work.PTGeometric.padEuc k 10 (by norm_num)).continuous.comp
        ((NormalTotal.continuous_vec E).comp (continuous_bundleToNormal E ND))⟩
  obtain ⟨G, hGproj, hGeval⟩ :=
    Grassmann.tautTotalMap P W (fun p => gtdMemPlane_padGaussEval E ND p)
  have hproj : ∀ p, (Grassmann.tautologicalBundle k 10).proj (G p)
      = Grassmann.padGaussFun E ND p.1 := fun p => hGproj p
  have heval : ∀ p, Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (NormalTotal.vec (bundleToNormal E ND p)) := fun p => hGeval p
  have hzero : ∀ p ∈ Work.Thom.zeroComplement (normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10) := by
    intro p hp
    rw [Work.Thom.mem_zeroComplement] at hp ⊢
    intro h0
    have h1 : Grassmann.evalVec (G p) = 0 :=
      gtdEvalVec_eq_zero_of_snd_eq_zero (G p) h0
    rw [heval p] at h1
    have h2 : NormalTotal.vec (bundleToNormal E ND p) = 0 := by
      refine Work.PTGeometric.padEuc_injective k 10 (by norm_num) ?_
      rw [map_zero]
      exact h1
    have h3 : Work.Thom.fibreNorm (normalBundle E ND) p = 0 := by
      rw [fibreNorm_eq_normalNorm]
      show ‖NormalTotal.vec (bundleToNormal E ND p)‖ = 0
      rw [h2, norm_zero]
    exact hp (norm_eq_zero.mp (by simpa [Work.Thom.fibreNorm] using h3))
  exact ⟨G, hzero, hproj, heval⟩

/-! ## The input `hcan` of `gaussBranch_uniform_full` -/

/-- **The canonical Gauss candidate of every piece is a local-degree class, up to ONE sign.**

This is the input `hcan` of `Work.ThomBordism.gaussBranch_uniform_full`, produced from the universal
local-degree class `Work.ThomBordism.localDegree_universalThomClass`.  The single sign is the
sign `s` with `Grassmann.tautologicalThomClass k 10 = s • u₀`. -/
theorem hcan_of_genuineTubeGeometry {k : ℕ} (hk : 1 ≤ k)
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8} (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) :
    ∃ t : ℤ, (t = 1 ∨ t = -1) ∧
      ∀ i, ∃ (ND : NormalData (Fam i) k (G.emb i).e)
        (Gp : C((normalBundle (G.emb i) ND).TotalSpace,
          (Grassmann.tautologicalBundle k 10).TotalSpace))
        (hgm : ∀ p ∈ Work.Thom.zeroComplement (normalBundle (G.emb i) ND),
          Gp p ∈ Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10)),
        (∀ p, (Grassmann.tautologicalBundle k 10).proj (Gp p)
            = Grassmann.padGaussFun (G.emb i) ND p.1) ∧
        (∀ p, Grassmann.evalVec (Gp p)
            = Work.PTGeometric.padEuc k 10 (by norm_num)
                (NormalTotal.vec (bundleToNormal (G.emb i) ND p))) ∧
        IsLocalDegreeClass (G.chart i) (G.g i) (G.hg i) G.hR (G.hbox i)
          (t • gtdU (G.emb i) ND Gp hgm) := by
  classical
  obtain ⟨u₀, huniv⟩ := localDegree_universalThomClass k hk
  obtain ⟨s, hs, hsτ⟩ := thomClass_eq_smul k (Grassmann.tautologicalThomClass k 10) u₀
  refine ⟨s, hs, fun i => ?_⟩
  obtain ⟨NDg, Gc, hgmc, σ, hσ, hpull, hbp, hvec, _hgauss⟩ := G.pulledThom_gauss i
  obtain ⟨Gp, hgmP, hbpP, hvecP⟩ := exists_plainGaussCandidate (G.emb i) NDg
  -- the branch comparison: the recorded candidate differs from the plain one by `η = ±1`
  have hbranch : gtdU (G.emb i) NDg Gc hgmc
      = (if σ = 1 then (1 : ℤ) else -1) • gtdU (G.emb i) NDg Gp hgmP :=
    gtdU_eq_zsmul_of_branch_aux_le hk (G.emb i) NDg NDg σ hσ Gc hgmc hbp hvec Gp hgmP hbpP hvecP
  -- the recorded class is a local-degree class
  have hldGc : IsLocalDegreeClass (G.chart i) (G.g i) (G.hg i) G.hR (G.hbox i)
      (gtdU (G.emb i) NDg Gc hgmc) := by
    rw [← hpull]
    exact G.localDegree i
  -- the universal class makes the plain candidate a local-degree class
  haveI : CompactSpace (NormalDiscSub (G.emb i) (G.ε i)) :=
    compactSpace_normalDiscSub (G.emb i) (G.ε i)
  haveI : ConnectedSpace (Fam i).pt := G.hconn i
  have hunivP : IsLocalDegreeClass (G.chart i) (G.g i) (G.hg i) G.hR (G.hbox i)
      (gtdUWith (G.emb i) NDg Gp hgmP u₀) :=
    huniv (G.emb i) NDg Gp hgmP hbpP hvecP (G.chart i) (G.q i)
      (G.chart i).isCompact_U G.hR (G.hbox i) (G.g i) (G.hg i) (G.hg2 i)
  -- the plain candidate is `s` times the universal class
  have hlin : gtdU (G.emb i) NDg Gp hgmP
      = s • gtdUWith (G.emb i) NDg Gp hgmP u₀ := by
    rw [gtdU_eq_gtdUWith]
    exact gtdUWith_eq_zsmul_of_tau_eq (G.emb i) NDg Gp hgmP hs hsτ
  -- non-degeneracy of the local-degree functional
  have hnd : ∃ x : Work.Thom.Coh ℤ 8 (TopCat.of (NormalTotal (G.emb i))),
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of (Fam i).pt)) 8
        ((Work.Thom.CohMap (zeroSectionNormal (G.emb i)) ℤ 8).hom x) (Fam i).c ≠ 0 :=
    exists_kronH_zeroSection_fund_ne_zero_ne (G.nonempty i) (G.emb i)
  -- the scaled universal class is a local-degree class, with the branch's sign
  have hldscaled : IsLocalDegreeClass (G.chart i) (G.g i) (G.hg i) G.hR (G.hbox i)
      (((if σ = 1 then (1 : ℤ) else -1) * s) •
        gtdUWith (G.emb i) NDg Gp hgmP u₀) := by
    rw [← smul_smul, ← hlin, ← hbranch]
    exact hldGc
  -- hence the two signs agree
  have heq : (if σ = 1 then (1 : ℤ) else -1) * s = 1 :=
    isLocalDegreeClass_zsmul_eq (E := G.emb i) (C := G.chart i) (g := G.g i) (hg := G.hg i)
      (hR := G.hR) (hbox := G.hbox i) (hnd := hnd)
      (U := gtdUWith (G.emb i) NDg Gp hgmP u₀)
      (a := (if σ = 1 then (1 : ℤ) else -1) * s) (b := 1) hldscaled (by rw [one_smul]; exact hunivP)
  have heta : (if σ = 1 then (1 : ℤ) else -1) = s := by
    have hs2 : s * s = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
    calc (if σ = 1 then (1 : ℤ) else -1)
        = ((if σ = 1 then (1 : ℤ) else -1) * s) * s := by rw [mul_assoc, hs2, mul_one]
      _ = s := by rw [heq, one_mul]
  refine ⟨NDg, Gp, hgmP, hbpP, hvecP, ?_⟩
  rw [hbranch, heta] at hldGc
  exact hldGc

/-- **The branch uniformity of `pulledThom_gauss`, with NO hypothesis beyond `1 ≤ k`.**

The field `Work.PTGeometric.GenuineTubeGeometry.pulledThom_gauss` records, per piece, a sign `s_i`
with which the oriented Gauss plane of the collapse is `padGaussFunM` (up to `ogFlip`).  Here we
prove that `s_i` is the *same* sign for every piece — the geometric input of the boundary
coordination of the last mile (`NOTE_SESSION64.md` §8-§9, `NOTE_SESSION63.md` §3 (4)).

This supersedes `Work.ThomBordism.gaussBranch_uniform` (which needed `Odd k` and
`ConnectedSpace (Fam i).pt`) and makes `Work.ThomBordism.gaussBranch_uniform_full` applicable. -/
theorem gaussBranch_uniform_of_universal {k : ℕ} (hk : 1 ≤ k)
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8} (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      ∀ i, ∃ (ND : NormalData (Fam i) k (G.emb i).e)
        (Gc : C((normalBundle (G.emb i) ND).TotalSpace,
          (Grassmann.tautologicalBundle k 10).TotalSpace))
        (hgm : ∀ p ∈ Work.Thom.zeroComplement (normalBundle (G.emb i) ND),
          Gc p ∈ Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10)),
        G.pulledThom i = gtdU (G.emb i) ND Gc hgm ∧
        (∀ p, (Grassmann.tautologicalBundle k 10).proj (Gc p)
            = (if s = 1 then id else Grassmann.ogFlip k 10)
                (Grassmann.padGaussFun (G.emb i) ND p.1)) ∧
        (∀ p, Grassmann.evalVec (Gc p)
            = Work.PTGeometric.padEuc k 10 (by norm_num)
                (NormalTotal.vec (bundleToNormal (G.emb i) ND p))) ∧
        (∀ (t : Fin (8 + k) → unitInterval),
          cubeToEuc (8 + k) G.R t ∈ (G.chart i).openTube →
            ∃ hne : alphaV (G.chart i) G.hR (G.hbox i) D.t₀ (G.J i) (G.hJ i)
                (G.g i) (G.hg i) t ≠ D.t₀,
              G.gauss ⟨alphaV (G.chart i) G.hR (G.hbox i) D.t₀ (G.J i) (G.hJ i)
                  (G.g i) (G.hg i) t, hne⟩ =
                (if s = 1 then id else Grassmann.ogFlip k G.mU)
                  (padGaussFunM (G.emb i) ND G.mU G.hmU
                    ((G.chart i).inv (cubeToEuc (8 + k) G.R t)).1.1)) :=
  gaussBranch_uniform_full hk G (hcan_of_genuineTubeGeometry hk G)

end

end Work.ThomBordism
