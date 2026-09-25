import Mathlib
import Submission.Work.Tower.ProPEndgame.Defs
import Submission.Work.GolodShafarevich.RelatorAug.Vfun_relator_mem_augIdeal

namespace Work.Tower.ProPEndgame

open Work.GolodShafarevich

/-- Let `φ : F_d ↠ G` be a *minimal* presentation of a nontrivial finite `p`-group `G` (the
hypothesis `hmin` says that no presentation of `G` has fewer generators).  Then for every
`w ∈ ker φ` the Fox derivative vector `Vfun φ w` has all its coordinates in the augmentation ideal
of `𝔽_p[G]`.

This is `Work.GolodShafarevich.RelatorAug.Vfun_relator_mem_augIdeal` with a relator replaced by an
arbitrary element of the kernel; the proof is the same: minimality forces every exponent sum
`expSum i w` to be divisible by `p` (`Work.GolodShafarevich.RelatorAug.p_dvd_expSum_of_mem_ker`,
which takes exactly these hypotheses and `hw : φ w = 1`), while the augmentation of `Vfun φ w i` is
`expSum i w` (`Work.GolodShafarevich.expSum_cast_eq_aug` and
`augAlgHom_groupAlgMap`), so it vanishes in `ZMod p`. -/
theorem Vfun_ker_mem_augIdeal (p : ℕ) (hp : Nat.Prime p) {d : ℕ} {G : Type} [Group G]
    [Fintype G] [Nontrivial G] (hG : IsPGroup p G) (φ : FreeGroup (Fin d) →* G)
    (hφ : Function.Surjective φ)
    (hmin : ∀ (d' : ℕ) (ψ : FreeGroup (Fin d') →* G), Function.Surjective ψ → d ≤ d')
    (w : FreeGroup (Fin d)) (hw : φ w = 1) (i : Fin d) :
    Work.GolodShafarevich.Vfun (ZMod p) φ w i ∈ Work.GolodShafarevich.augIdeal (ZMod p) G := by
  have hdvd : (p : ℤ) ∣ expSum i w :=
    RelatorAug.p_dvd_expSum_of_mem_ker hp hG φ hφ hmin hw i
  rw [mem_augIdeal_iff]
  have h2 : augAlgHom (ZMod p) G (Vfun (ZMod p) φ w i) = ((expSum i w : ℤ) : ZMod p) := by
    rw [Vfun_apply, augAlgHom_groupAlgMap, ← expSum_cast_eq_aug]
  rw [h2, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact_mod_cast hdvd

end Work.Tower.ProPEndgame
