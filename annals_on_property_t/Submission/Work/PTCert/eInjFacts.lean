import Mathlib
import Submission.Work.PTCert.eAux

namespace Work.PTCert

/-- The elements of `eAll` are distinct automorphisms (`eltC` is injective on `eAll`).
Recipe: `Submission.PTCert.C.efaith_ok : eFaithfulOK eAll = true` is
`strictInc (msortK 40 (eAll.map modelKey)) = true`; with `Work.PTCert.strictInc_nodup`,
`Work.PTCert.msortK_perm 40 (eAll.map modelKey)` and `List.Perm.nodup_iff` get
`(eAll.map modelKey).Nodup`, then `List.inj_on_of_nodup_map` (or `List.nodup_map_iff_inj_on`)
gives injectivity of `modelKey` on `eAll`.  Apply the hypothesis `ModelKeyFaithful` with
`a = z/128`, `b = z%128`, `a' = z'/128`, `b' = z'%128` (the bounds come from `hlb`), and rewrite
`128 * (z / 128) + z % 128 = z` (`Nat.div_add_mod`).  Note `eltC z = b1 5 (z/128) * b1 5 (z%128)`
is definitionally `Submission.PTCert.eltC`, so the hypothesis `eltC z = eltC z'` is exactly what
`ModelKeyFaithful` needs. -/
theorem eInjFacts (hKF : Submission.PTCert.ModelKeyFaithful)
    (hlb : ∀ z ∈ Submission.PTCert.D.eAll, z / 128 < 81 ∧ z % 128 < 81) :
    ∀ z ∈ Submission.PTCert.D.eAll, ∀ z' ∈ Submission.PTCert.D.eAll,
      Submission.PTCert.eltC z = Submission.PTCert.eltC z' → z = z' := by
  -- `modelKey` is injective on `eAll`, from the kernel check `eFaithfulOK eAll = true`
  have hstrict : Submission.PTCert.strictInc
      (Submission.PTCert.msortK 40
        (Submission.PTCert.D.eAll.map Submission.PTCert.modelKey)) = true :=
    Submission.PTCert.C.efaith_ok
  have hnodupS := strictInc_nodup
    (Submission.PTCert.msortK 40
      (Submission.PTCert.D.eAll.map Submission.PTCert.modelKey)) hstrict
  have hperm := msortK_perm 40
    (Submission.PTCert.D.eAll.map Submission.PTCert.modelKey)
  have hnodup : (Submission.PTCert.D.eAll.map Submission.PTCert.modelKey).Nodup :=
    (List.Perm.nodup_iff hperm).mp hnodupS
  have hinj := List.inj_on_of_nodup_map hnodup
  intro z hz z' hz' h
  refine hinj hz hz' ?_
  -- `eltC z = b1 5 (z / 128) * b1 5 (z % 128)`, so `h` is the hypothesis of `ModelKeyFaithful`
  have h1 := hlb z hz
  have h2 := hlb z' hz'
  have h3 : Submission.PTCert.modelKey (128 * (z / 128) + z % 128)
      = Submission.PTCert.modelKey (128 * (z' / 128) + z' % 128) :=
    hKF (z / 128) (z % 128) (z' / 128) (z' % 128) h1.1 h1.2 h2.1 h2.2 h
  rwa [Nat.div_add_mod z 128, Nat.div_add_mod z' 128] at h3

end Work.PTCert
