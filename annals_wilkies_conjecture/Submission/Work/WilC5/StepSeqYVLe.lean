import Mathlib
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.ValueOrder
import Submission.Work.WilC5.ValuesLemmas
import Submission.Work.WilC5.StepSeq
import Submission.Work.WilC5.S4StepNewSetup
import Submission.Work.WilC5.YVLeAuxDefs
import Submission.Work.WilC5.VLe_iff_VLeAux
import Submission.Work.WilC5.Reduct
import Submission.Work.WilC5.stdPart
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.S4ExpG.Glue
import Submission.Work.WilC5.LRcReduct

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. Two auxiliary lemmas

Before the main theorem we record

* `vle_iff_inv_mul`: `VLe x b` for `x > 0`, in the "divided" form `b/(N+1) ≤ x` and
  `-(b/(N+1)) ≤ x` (`VLe x b` means "`b` is bounded by a natural multiple of `x`", so for `x > 0`
  it says that `x` is not infinitesimal relative to `b`);
* `yvle_realConst_facts`: at the `rexp`-reduct of a model of `TE`, the real constants are the
  field elements — `realConst K (N:ℝ) = (N:K)` and `realConst K ((N:ℝ)+1)⁻¹ = ((N:K)+1)⁻¹`.
  These are the two facts that turn the `B`-element `b · c_{(N+1)⁻¹}` into `b/(N+1)`. -/

/-- **`VLe x b`, for `x > 0`, in the divided form.** -/
theorem vle_iff_inv_mul {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {x b : F} (hx : 0 < x) :
    VLe x b ↔ ∃ M : ℕ, ((M : F) + 1)⁻¹ * b ≤ x ∧ -(((M : F) + 1)⁻¹ * b) ≤ x := by
  constructor
  · rintro ⟨M, hM⟩
    have hne : ((M : F) + 1) ≠ 0 := by positivity
    have hinv : (0 : F) ≤ ((M : F) + 1)⁻¹ := by positivity
    have hcancel : ∀ z : F, ((M : F) + 1)⁻¹ * (((M : F) + 1) * z) = z := by
      intro z; rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    rw [abs_of_pos hx] at hM
    refine ⟨M, ?_, ?_⟩
    · have h := mul_le_mul_of_nonneg_left (le_trans (le_abs_self b) hM) hinv
      rwa [hcancel x] at h
    · have h := mul_le_mul_of_nonneg_left (le_trans (neg_le_abs b) hM) hinv
      rw [hcancel x] at h
      have hneg : ((M : F) + 1)⁻¹ * (-b) = -(((M : F) + 1)⁻¹ * b) := by rw [mul_neg]
      rwa [hneg] at h
  · rintro ⟨M, h1, h2⟩
    have hne : ((M : F) + 1) ≠ 0 := by positivity
    have hpos : (0 : F) < (M : F) + 1 := by positivity
    have hcancel : ∀ z : F, ((M : F) + 1) * (((M : F) + 1)⁻¹ * z) = z := by
      intro z; rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    refine ⟨M, ?_⟩
    rw [abs_of_pos hx]
    refine abs_le'.mpr ⟨?_, ?_⟩
    · have h := mul_le_mul_of_nonneg_left h1 (le_of_lt hpos)
      rwa [hcancel b] at h
    · have h := mul_le_mul_of_nonneg_left h2 (le_of_lt hpos)
      rw [mul_neg, hcancel b] at h
      exact h

section RealConstFacts

variable {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (hK : K ⊨ WilkiesDesign.CG.TE)
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)

include hK hrexp hadd hmul hone hleneg

/-- **The real constants of a model of `TE`, at the `rexp`-reduct, are the field elements.**

The proof pins the `Ring`/`rexpL`/`constantsOn` instances to the reduct ones (the pattern of
`Work.WilC5.StepSeqLogDominated`), so that `Work.WilC5.reductStruct_eq_withConstants` applies and
`Work.WilC5.realConst_natCast`, `Work.WilC5.realConst_inv` become available; the results are then
transported back along `Work.WilC5.realConst_reduct_synth`. -/
theorem yvle_realConst_facts :
    (∀ N : ℕ, Work.WilC5.realConst K (N : ℝ) = (N : K)) ∧
    (∀ M : ℕ, Work.WilC5.realConst K (((M : ℝ) + 1)⁻¹) = ((M : K) + 1)⁻¹) := by
  have hTE : K ⊨ WilkiesDesign.CG.TE := hK
  let myCR : FirstOrder.Ring.CompatibleRing K :=
    { toStructure := @Work.WilC5.lrcRingReduct K (Work.WilC5.instStructureLRcOfLEc K)
      funMap_add := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hys : ys = ![ys 0, ys 1] := by funext i; fin_cases i <;> rfl
        rw [hys]; exact hadd _ _
      funMap_mul := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hys : ys = ![ys 0, ys 1] := by funext i; fin_cases i <;> rfl
        rw [hys]; exact hmul _ _
      funMap_neg := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hys : ys = ![ys 0] := by funext i; fin_cases i <;> rfl
        rw [hys]; exact Work.WilC5.S4ExpF.negE_eq_neg hTE hadd _
      funMap_zero := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        rw [show ys = default from Subsingleton.elim _ _]
        exact Work.WilC5.S4ExpF.zeroE_eq_zero hTE hadd
      funMap_one := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        rw [show ys = default from Subsingleton.elim _ _]
        exact hone }
  letI : FirstOrder.Ring.CompatibleRing K := myCR
  letI hRX : WilkiesDesign.CG.rexpL.Structure K :=
    @Work.WilC5.lrcRexpReduct K (Work.WilC5.reductStruct K)
  letI hCT : (FirstOrder.Language.constantsOn ℝ).Structure K :=
    @Work.WilC5.lrcConstReduct K (Work.WilC5.reductStruct K)
  have hstruct : (Work.WilC5.reductStruct K : LRc.Structure K) = LR.withConstantsStructure ℝ :=
    Work.WilC5.reductStruct_eq_withConstants (M := K)
  have hTR : @FirstOrder.Language.Theory.Model LRc K (LR.withConstantsStructure ℝ)
      WilkiesDesign.CG.TR :=
    hstruct ▸ (Work.WilC5.reduct_model_TR K hTE)
  have hnatC : ∀ N : ℕ,
      @Work.WilC5.realConst K (LR.withConstantsStructure ℝ) (N : ℝ) = (N : K) :=
    fun N => @Work.WilC5.realConst_natCast K _ _ _ _ _ _ hTR N
  have hinvC : ∀ M : ℕ,
      @Work.WilC5.realConst K (LR.withConstantsStructure ℝ) (((M : ℝ) + 1)⁻¹)
        = ((M : K) + 1)⁻¹ := by
    intro M
    rw [@Work.WilC5.realConst_inv K _ _ _ _ _ _ hTR (((M : ℝ) + 1)) (by positivity),
      @Work.WilC5.realConst_natCast_add_one K _ _ _ _ _ _ hTR M]
  exact ⟨fun N => (Work.WilC5.realConst_reduct_synth (M := K) N).trans (hnatC N),
    fun M => (Work.WilC5.realConst_reduct_synth (M := K) (((M : ℝ) + 1)⁻¹)).trans (hinvC M)⟩

end RealConstFacts

/-! ## 2. The `B`-element interpreting a constant symbol -/

section BconstDef

variable {K : Type} [WilkiesDesign.CG.LRc.Structure K]

/-- The element of the substructure `B` interpreting the constant symbol attached to `r : ℝ`. -/
def Bconst (B : WilkiesDesign.CG.LRc.Substructure K) (r : ℝ) : ↥B :=
  @Structure.funMap WilkiesDesign.CG.LRc ↥B
    (FirstOrder.Language.Substructure.inducedStructure (S := B)) 0 (Sum.inr r) default

end BconstDef

/-- **The archimedean comparison with the base `B` transfers from `xᵢ` to `yᵢ`.**  If `yᵢ` realises
the image under `τ` of the cut of `xᵢ` over `B` (`hcutB`), then for every `b ∈ B` the archimedean
comparisons of `xᵢ` with `b` transfer to those of `yᵢ` with `τ b`: `VLe b xᵢ ↔ VLe (τ b) yᵢ` and
`VLe xᵢ b ↔ VLe yᵢ (τ b)`.  (The proof uses the cut realisation at the `B`-elements `(N+1)|b|` and
`-(N+1)|b|` respectively `|b|/(N+1)` and `-|b|/(N+1)`, so only that `τ` preserves the ordered ring
operations and the natural constants is needed.  `VLe a b` means "`b` is bounded by a natural
multiple of `a`".) -/
theorem StepSeqYVLe
    {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (hK : K ⊨ WilkiesDesign.CG.TE) (hL : L ⊨ WilkiesDesign.CG.TE)
    (hrexpK : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (honeK : (Work.WilC5.oneE : K) = 1)
    (hlenegK : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (hrexpL : ∀ x : L, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL L _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y)
    (hmulL : ∀ x y : L, Work.WilC5.mulE x y = x * y)
    (honeL : (Work.WilC5.oneE : L) = 1)
    (hlenegL : ∀ x y : L, Work.WilC5.leE x y ↔ x ≤ y)
    {B : WilkiesDesign.CG.LRc.Substructure K}
    (τ : WilkiesDesign.CG.LRc.Embedding ↥B L)
    (S : Work.WilC5.StepSeq B)
    (hnew : Work.WilC5.StepSeq.ValueNewAll S)
    {y0 : L}
    (hcutB : ∀ i : ℕ, ∀ b : ↥B,
      (((b : K) < S.xs i ↔ (τ b : L) < Work.WilC5.StepSeq.ys B τ S y0 i) ∧
       (S.xs i < (b : K) ↔ Work.WilC5.StepSeq.ys B τ S y0 i < (τ b : L))))
    (i : ℕ) (b : ↥B) :
    (Work.WilC5.VLe (b : K) (S.xs i) ↔
        Work.WilC5.VLe (τ b : L) (Work.WilC5.StepSeq.ys B τ S y0 i)) ∧
    (Work.WilC5.VLe (S.xs i) (b : K) ↔
        Work.WilC5.VLe (Work.WilC5.StepSeq.ys B τ S y0 i) (τ b : L)) := by
  -- ## 0. `K` and `L` satisfy `TR` through their `rexp`-reducts
  haveI hTRK : @FirstOrder.Language.Theory.Model WilkiesDesign.CG.LRc K (inferInstance)
      WilkiesDesign.CG.TR := Work.WilC5.reduct_model_TR K hK
  haveI hTRL : @FirstOrder.Language.Theory.Model WilkiesDesign.CG.LRc L (inferInstance)
      WilkiesDesign.CG.TR := Work.WilC5.reduct_model_TR L hL
  -- ## 1. The ring symbols of `LRc` against the field operations
  have hMulK : ∀ a c : K, (@Structure.funMap WilkiesDesign.CG.LRc K (inferInstance) 2
      (Sum.inl (Sum.inl Ring.mulFunc)) ![a, c] : K) = a * c :=
    fun a c => (Work.WilC5.reductStruct_funMap_ring K Ring.mulFunc ![a, c]).trans (hmulK a c)
  have hMulL : ∀ a c : L, (@Structure.funMap WilkiesDesign.CG.LRc L (inferInstance) 2
      (Sum.inl (Sum.inl Ring.mulFunc)) ![a, c] : L) = a * c :=
    fun a c => (Work.WilC5.reductStruct_funMap_ring L Ring.mulFunc ![a, c]).trans (hmulL a c)
  have hNegK : ∀ a : K, (@Structure.funMap WilkiesDesign.CG.LRc K (inferInstance) 1
      (Sum.inl (Sum.inl Ring.negFunc)) ![a] : K) = -a :=
    fun a => (Work.WilC5.reductStruct_funMap_ring K Ring.negFunc ![a]).trans
      (Work.WilC5.S4ExpF.negE_eq_neg hK haddK a)
  have hNegL : ∀ a : L, (@Structure.funMap WilkiesDesign.CG.LRc L (inferInstance) 1
      (Sum.inl (Sum.inl Ring.negFunc)) ![a] : L) = -a :=
    fun a => (Work.WilC5.reductStruct_funMap_ring L Ring.negFunc ![a]).trans
      (Work.WilC5.S4ExpF.negE_eq_neg hL haddL a)
  have hZeroK : (@Structure.funMap WilkiesDesign.CG.LRc K (inferInstance) 0
      (Sum.inl (Sum.inl Ring.zeroFunc)) default : K) = 0 :=
    (Work.WilC5.reductStruct_funMap_ring K Ring.zeroFunc default).trans
      (Work.WilC5.S4ExpF.zeroE_eq_zero hK haddK)
  have hZeroL : (@Structure.funMap WilkiesDesign.CG.LRc L (inferInstance) 0
      (Sum.inl (Sum.inl Ring.zeroFunc)) default : L) = 0 :=
    (Work.WilC5.reductStruct_funMap_ring L Ring.zeroFunc default).trans
      (Work.WilC5.S4ExpF.zeroE_eq_zero hL haddL)
  -- ## 2. The real constants against the field elements
  obtain ⟨hNatK, hInvK⟩ := yvle_realConst_facts (K := K) hK hrexpK haddK hmulK honeK hlenegK
  obtain ⟨hNatL, hInvL⟩ := yvle_realConst_facts (K := L) hL hrexpL haddL hmulL honeL hlenegL
  -- ## 3. The `B`-elements interpreting the ring symbols and the constants
  have hCoe : ∀ {n : ℕ} (f : WilkiesDesign.CG.LRc.Functions n) (v : Fin n → ↥B),
      ((@Structure.funMap WilkiesDesign.CG.LRc ↥B (inferInstance) n f v : ↥B) : K)
        = @Structure.funMap WilkiesDesign.CG.LRc K (inferInstance) n f (fun j => (v j : K)) :=
    fun f v => FirstOrder.Language.Embedding.map_fun (Substructure.subtype B) f v
  have hCoeTau : ∀ {n : ℕ} (f : WilkiesDesign.CG.LRc.Functions n) (v : Fin n → ↥B),
      τ (@Structure.funMap WilkiesDesign.CG.LRc ↥B (inferInstance) n f v)
        = @Structure.funMap WilkiesDesign.CG.LRc L (inferInstance) n f (fun j => τ (v j)) :=
    fun f v => FirstOrder.Language.Embedding.map_fun τ f v
  have hBmul_coe : ∀ c d : ↥B, ((Bmul B c d : ↥B) : K) = (c : K) * (d : K) := by
    intro c d
    have h := hCoe (Sum.inl (Sum.inl Ring.mulFunc)) ![c, d]
    simp only [Bmul]
    refine h.trans ?_
    rw [show (fun j : Fin 2 => (((![c, d]) j : ↥B) : K)) = ![(c : K), (d : K)] from by
      funext j; fin_cases j <;> rfl]
    exact hMulK (c : K) (d : K)
  have hBmul_tau : ∀ c d : ↥B, τ (Bmul B c d) = (τ c) * (τ d) := by
    intro c d
    have h := hCoeTau (Sum.inl (Sum.inl Ring.mulFunc)) ![c, d]
    simp only [Bmul]
    refine h.trans ?_
    rw [show (fun j : Fin 2 => τ (((![c, d]) j : ↥B))) = ![τ c, τ d] from by
      funext j; fin_cases j <;> rfl]
    exact hMulL (τ c) (τ d)
  have hBneg_coe : ∀ c : ↥B, ((Bneg B c : ↥B) : K) = -(c : K) := by
    intro c
    have h := hCoe (Sum.inl (Sum.inl Ring.negFunc)) ![c]
    simp only [Bneg]
    refine h.trans ?_
    rw [show (fun j : Fin 1 => (((![c]) j : ↥B) : K)) = ![(c : K)] from by
      funext j; fin_cases j <;> rfl]
    exact hNegK (c : K)
  have hBneg_tau : ∀ c : ↥B, τ (Bneg B c) = -(τ c) := by
    intro c
    have h := hCoeTau (Sum.inl (Sum.inl Ring.negFunc)) ![c]
    simp only [Bneg]
    refine h.trans ?_
    rw [show (fun j : Fin 1 => τ (((![c]) j : ↥B))) = ![τ c] from by
      funext j; fin_cases j <;> rfl]
    exact hNegL (τ c)
  have hBconst_coe : ∀ r : ℝ, ((Bconst B r : ↥B) : K) = realConst K r := by
    intro r
    have h := FirstOrder.Language.Embedding.map_fun (Substructure.subtype B)
      (Sum.inr r : WilkiesDesign.CG.LRc.Functions 0) (default : Fin 0 → ↥B)
    simp only [Bconst]
    refine h.trans ?_
    rw [show ((Substructure.subtype B) ∘ (default : Fin 0 → ↥B)) = (default : Fin 0 → K)
      from Subsingleton.elim _ _]
    rw [show (default : Fin 0 → K) = ![] from Subsingleton.elim _ _]
    exact (Work.WilC5.realConst_funMap K r).symm
  have hBconst_tau : ∀ r : ℝ, τ (Bconst B r) = realConst L r := by
    intro r
    have h := FirstOrder.Language.Embedding.map_fun τ
      (Sum.inr r : WilkiesDesign.CG.LRc.Functions 0) (default : Fin 0 → ↥B)
    simp only [Bconst]
    refine h.trans ?_
    rw [show (τ ∘ (default : Fin 0 → ↥B)) = (default : Fin 0 → L) from Subsingleton.elim _ _]
    rw [show (default : Fin 0 → L) = ![] from Subsingleton.elim _ _]
    exact (Work.WilC5.realConst_funMap L r).symm
  have hBzero_coe : ((Bzero B : ↥B) : K) = 0 := by
    have h := hCoe (Sum.inl (Sum.inl Ring.zeroFunc)) (default : Fin 0 → ↥B)
    simp only [Bzero]
    refine h.trans ?_
    rw [show (fun j : Fin 0 => (((default : Fin 0 → ↥B) j : ↥B) : K)) = (default : Fin 0 → K)
      from Subsingleton.elim _ _]
    exact hZeroK
  have hBzero_tau : τ (Bzero B) = 0 := by
    have h := FirstOrder.Language.Embedding.map_fun τ
      (Sum.inl (Sum.inl Ring.zeroFunc)) (default : Fin 0 → ↥B)
    simp only [Bzero]
    refine h.trans ?_
    rw [show (τ ∘ (default : Fin 0 → ↥B)) = (default : Fin 0 → L) from Subsingleton.elim _ _]
    exact hZeroL
  -- ## 4. The cut, in the `≤` form
  have hcut : ∀ c : ↥B,
      (S.xs i ≤ (c : K) ↔ StepSeq.ys B τ S y0 i ≤ (τ c : L)) ∧
      ((c : K) ≤ S.xs i ↔ (τ c : L) ≤ StepSeq.ys B τ S y0 i) := by
    intro c
    obtain ⟨h1, h2⟩ := hcutB i c
    exact ⟨⟨fun h => not_lt.mp ((not_congr h1).mp (not_lt.mpr h)),
            fun h => not_lt.mp ((not_congr h1).mpr (not_lt.mpr h))⟩,
           ⟨fun h => not_lt.mp ((not_congr h2).mp (not_lt.mpr h)),
            fun h => not_lt.mp ((not_congr h2).mpr (not_lt.mpr h))⟩⟩
  -- ## 5. The first comparison, by way of `VLeAux`
  have hfirst : VLe (b : K) (S.xs i) ↔
      VLe (τ b : L) (StepSeq.ys B τ S y0 i) := by
    have key : VLeAux (b : K) (S.xs i) ↔ VLeAux (τ b : L) (StepSeq.ys B τ S y0 i) := by
      unfold VLeAux
      constructor
      · rintro ⟨n, h1, h2⟩
        have hcK : ((Bmul B (Bconst B (n : ℝ)) b : ↥B) : K) = (n : K) * (b : K) :=
          (hBmul_coe _ _).trans (by rw [hBconst_coe, hNatK n])
        have hcL : τ (Bmul B (Bconst B (n : ℝ)) b) = (n : L) * (τ b) :=
          (hBmul_tau _ _).trans (by rw [hBconst_tau, hNatL n])
        have hdK : ((Bneg B (Bmul B (Bconst B (n : ℝ)) b) : ↥B) : K) = -((n : K) * (b : K)) :=
          (hBneg_coe _).trans (by rw [hcK])
        have hdL : τ (Bneg B (Bmul B (Bconst B (n : ℝ)) b)) = -((n : L) * (τ b)) :=
          (hBneg_tau _).trans (by rw [hcL])
        have e1 := (hcut (Bmul B (Bconst B (n : ℝ)) b)).1
        have e2 := (hcut (Bmul B (Bconst B (n : ℝ)) b)).2
        have e3 := (hcut (Bneg B (Bmul B (Bconst B (n : ℝ)) b))).1
        have e4 := (hcut (Bneg B (Bmul B (Bconst B (n : ℝ)) b))).2
        rw [hcK, hcL] at e1 e2
        rw [hdK, hdL] at e3 e4
        exact ⟨n, h1.elim (fun h => Or.inl (e1.mp h)) (fun h => Or.inr (e3.mp h)),
          h2.elim (fun h => Or.inl (e2.mp h)) (fun h => Or.inr (e4.mp h))⟩
      · rintro ⟨n, h1, h2⟩
        have hcK : ((Bmul B (Bconst B (n : ℝ)) b : ↥B) : K) = (n : K) * (b : K) :=
          (hBmul_coe _ _).trans (by rw [hBconst_coe, hNatK n])
        have hcL : τ (Bmul B (Bconst B (n : ℝ)) b) = (n : L) * (τ b) :=
          (hBmul_tau _ _).trans (by rw [hBconst_tau, hNatL n])
        have hdK : ((Bneg B (Bmul B (Bconst B (n : ℝ)) b) : ↥B) : K) = -((n : K) * (b : K)) :=
          (hBneg_coe _).trans (by rw [hcK])
        have hdL : τ (Bneg B (Bmul B (Bconst B (n : ℝ)) b)) = -((n : L) * (τ b)) :=
          (hBneg_tau _).trans (by rw [hcL])
        have e1 := (hcut (Bmul B (Bconst B (n : ℝ)) b)).1
        have e2 := (hcut (Bmul B (Bconst B (n : ℝ)) b)).2
        have e3 := (hcut (Bneg B (Bmul B (Bconst B (n : ℝ)) b))).1
        have e4 := (hcut (Bneg B (Bmul B (Bconst B (n : ℝ)) b))).2
        rw [hcK, hcL] at e1 e2
        rw [hdK, hdL] at e3 e4
        exact ⟨n, h1.elim (fun h => Or.inl (e1.mpr h)) (fun h => Or.inr (e3.mpr h)),
          h2.elim (fun h => Or.inl (e2.mpr h)) (fun h => Or.inr (e4.mpr h))⟩
    exact (VLe_iff_VLeAux (b : K) (S.xs i)).trans
      (key.trans (VLe_iff_VLeAux (τ b : L) (StepSeq.ys B τ S y0 i)).symm)
  -- ## 6. The second comparison, by way of the divided form
  have hsecond : VLe (S.xs i) (b : K) ↔
      VLe (StepSeq.ys B τ S y0 i) (τ b : L) := by
    have hxpos : 0 < S.xs i :=
      (Work.WilC5.S4ExpF.leE_zero_iff hK haddK hlenegK (S.xs i)).mp (S.hpos i)
    have hypos : 0 < StepSeq.ys B τ S y0 i := by
      have h := (hcutB i (Bzero B)).1
      rw [hBzero_coe, hBzero_tau] at h
      exact h.mp hxpos
    have key : (∃ M : ℕ, ((M : K) + 1)⁻¹ * (b : K) ≤ S.xs i ∧
          -(((M : K) + 1)⁻¹ * (b : K)) ≤ S.xs i) ↔
        (∃ M : ℕ, ((M : L) + 1)⁻¹ * (τ b) ≤ StepSeq.ys B τ S y0 i ∧
          -(((M : L) + 1)⁻¹ * (τ b)) ≤ StepSeq.ys B τ S y0 i) := by
      constructor
      · rintro ⟨M, h1, h2⟩
        have hcK : ((Bmul B (Bconst B (((M : ℝ) + 1)⁻¹)) b : ↥B) : K)
            = ((M : K) + 1)⁻¹ * (b : K) :=
          (hBmul_coe _ _).trans (by rw [hBconst_coe, hInvK M])
        have hcL : τ (Bmul B (Bconst B (((M : ℝ) + 1)⁻¹)) b)
            = ((M : L) + 1)⁻¹ * (τ b) :=
          (hBmul_tau _ _).trans (by rw [hBconst_tau, hInvL M])
        have hdK : ((Bneg B (Bmul B (Bconst B (((M : ℝ) + 1)⁻¹)) b) : ↥B) : K)
            = -(((M : K) + 1)⁻¹ * (b : K)) := (hBneg_coe _).trans (by rw [hcK])
        have hdL : τ (Bneg B (Bmul B (Bconst B (((M : ℝ) + 1)⁻¹)) b))
            = -(((M : L) + 1)⁻¹ * (τ b)) := (hBneg_tau _).trans (by rw [hcL])
        have e1 := (hcut (Bmul B (Bconst B (((M : ℝ) + 1)⁻¹)) b)).2
        have e2 := (hcut (Bneg B (Bmul B (Bconst B (((M : ℝ) + 1)⁻¹)) b))).2
        rw [hcK, hcL] at e1
        rw [hdK, hdL] at e2
        exact ⟨M, e1.mp h1, e2.mp h2⟩
      · rintro ⟨M, h1, h2⟩
        have hcK : ((Bmul B (Bconst B (((M : ℝ) + 1)⁻¹)) b : ↥B) : K)
            = ((M : K) + 1)⁻¹ * (b : K) :=
          (hBmul_coe _ _).trans (by rw [hBconst_coe, hInvK M])
        have hcL : τ (Bmul B (Bconst B (((M : ℝ) + 1)⁻¹)) b)
            = ((M : L) + 1)⁻¹ * (τ b) :=
          (hBmul_tau _ _).trans (by rw [hBconst_tau, hInvL M])
        have hdK : ((Bneg B (Bmul B (Bconst B (((M : ℝ) + 1)⁻¹)) b) : ↥B) : K)
            = -(((M : K) + 1)⁻¹ * (b : K)) := (hBneg_coe _).trans (by rw [hcK])
        have hdL : τ (Bneg B (Bmul B (Bconst B (((M : ℝ) + 1)⁻¹)) b))
            = -(((M : L) + 1)⁻¹ * (τ b)) := (hBneg_tau _).trans (by rw [hcL])
        have e1 := (hcut (Bmul B (Bconst B (((M : ℝ) + 1)⁻¹)) b)).2
        have e2 := (hcut (Bneg B (Bmul B (Bconst B (((M : ℝ) + 1)⁻¹)) b))).2
        rw [hcK, hcL] at e1
        rw [hdK, hdL] at e2
        exact ⟨M, e1.mpr h1, e2.mpr h2⟩
    exact (vle_iff_inv_mul hxpos).trans
      (key.trans (vle_iff_inv_mul hypos).symm)
  exact ⟨hfirst, hsecond⟩

end Work.WilC5
