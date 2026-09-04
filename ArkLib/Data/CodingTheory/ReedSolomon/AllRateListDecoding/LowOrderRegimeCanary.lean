/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.LowOrderRegime

/-!
# Boundary canaries for the order-zero Reed--Solomon regime

The quarter-gap branch is not a uniqueness theorem. Over `ZMod 5`, four distinct evaluation
points and the received word `(0, 0, 1, 1)` contain both constant zero and constant one at the exact
quarter-gap threshold `1 + ceil((1/4) * 4) = 2`. This concrete example rejects an accidental
strengthening of the quarter-gap branch to list size one and exercises the actual ceiling-based
threshold.
-/

namespace ReedSolomon
namespace AllRateListDecoding

noncomputable section

local instance lowOrderCanaryPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

private def quarterCanaryDomain : Fin 4 ↪ ZMod 5 where
  toFun i := (i : ℕ)
  inj' i j hij := by
    apply Fin.ext
    have hval := congrArg ZMod.val hij
    simpa [ZMod.val_natCast_of_lt (by omega : (i : ℕ) < 5),
      ZMod.val_natCast_of_lt (by omega : (j : ℕ) < 5)] using hval

private def quarterCanaryReceived : Fin 4 → ZMod 5 := fun i =>
  if (i : ℕ) < 2 then 0 else 1

private def constantMessage (a : ZMod 5) : ListDecoding.MessagePolynomial (ZMod 5) 1 :=
  ⟨Polynomial.C a, Polynomial.mem_degreeLT.mpr
    (Polynomial.degree_C_le.trans_lt (by norm_num))⟩

/-- Two distinct constant polynomials meet the quarter-gap threshold in the same received word. -/
example :
    ∃ p p' : ListDecoding.MessagePolynomial (ZMod 5) 1,
      p ≠ p' ∧
        p ∈ agreeingPolynomials quarterCanaryDomain 1
          (agreementThreshold (1 / 4 : ℝ) 4 1) quarterCanaryReceived ∧
        p' ∈ agreeingPolynomials quarterCanaryDomain 1
          (agreementThreshold (1 / 4 : ℝ) 4 1) quarterCanaryReceived := by
  refine ⟨constantMessage 0, constantMessage 1, ?_, ?_, ?_⟩
  · intro h
    have hcoeff := congrArg (fun p : ListDecoding.MessagePolynomial (ZMod 5) 1 =>
      (p : Polynomial (ZMod 5)).coeff 0) h
    norm_num [constantMessage] at hcoeff
  · norm_num [agreeingPolynomials, agreementThreshold, quarterCanaryDomain,
      quarterCanaryReceived, constantMessage, ReedSolomon.evalOnPoints, Code.agree]
    decide
  · norm_num [agreeingPolynomials, agreementThreshold, quarterCanaryDomain,
      quarterCanaryReceived, constantMessage, ReedSolomon.evalOnPoints, Code.agree]
    decide

end
end AllRateListDecoding
end ReedSolomon
