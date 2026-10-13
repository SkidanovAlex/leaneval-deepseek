import Mathlib
import Submission.Work.DSM5b.HCF.LksAux

namespace Work.DSM5b.HCF

universe u

/-- The transport of a coefficient of a coefficient system along an equality of finsets commutes
with the scalar multiplication. -/
lemma coeffSys_cast_smul {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]
    (𝒜 : CoeffSys R ι) {S T : Finset ι} (e : S = T) (c : R) (v : 𝒜.M S) :
    e ▸ (c • v) = c • (e ▸ v) := by
  cases e
  rfl

/-- The block value `gBlockVal` is insensitive to the presentation of the block: the transport of
the value computed on `S` along an equality `e : S = T` is the value computed on `T`.  (The
cardinality witnesses are proofs of propositions, hence irrelevant.) -/
lemma gBlockVal_cast {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι] [LinearOrder ι]
    (𝒜 : CoeffSys R ι) (k q : ℕ) (y : Stc (CoeffSys.exactlyCoeff 𝒜 k) q)
    {S T : Finset ι} (e : S = T) (hS : q + 1 = S.card) (hT : q + 1 = T.card) :
    e ▸ gBlockVal 𝒜 k q y S hS = gBlockVal 𝒜 k q y T hT := by
  cases e
  exact congrArg (fun h => gBlockVal 𝒜 k q y S h) (Subsingleton.elim hS hT)

theorem gExtend_block_eq {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι] [LinearOrder ι]
    (𝒜 : Work.DSM5b.CoeffSys R ι) (k q : ℕ) (hk : q + 1 = k)
    (y : Work.DSM5b.Stc (Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k) q)
    (S₀ : Finset ι) (hS : S₀.card = k) :
    (fun σ : Work.DSM5b.HCF.GSurjIdx S₀ q =>
        (Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k).res (le_of_eq σ.2)
          (Work.DSM5b.HCF.gExtend 𝒜 k q hk y σ.1))
      = fun σ : Work.DSM5b.HCF.GSurjIdx S₀ q =>
          Work.DSM5b.HCF.gSignOfR (R := R) σ (hk.trans hS.symm) •
            Work.DSM5b.HCF.gBlockVal 𝒜 k q y S₀ (hk.trans hS.symm) := by
  funext σ
  obtain ⟨τ, hτ⟩ := σ
  have hcard : (Work.DSM5b.tupRng τ).card = k := by rw [hτ]; exact hS
  rw [gExtend_of_card 𝒜 k q hk y τ hcard]
  rw [htcAbove_res_eq_cast (Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k) hτ]
  rw [coeffSys_cast_smul (Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k) hτ]
  rw [gSignOfR_congr_block (S₀ := Work.DSM5b.tupRng τ) (S₀' := S₀) (q := q)
    (hk.trans hcard.symm) (hk.trans hS.symm) hτ rfl hτ]
  rw [gBlockVal_cast 𝒜 k q y hτ (hk.trans hcard.symm) (hk.trans hS.symm)]

end Work.DSM5b.HCF
