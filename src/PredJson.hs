{-# OPTIONS -Wall #-}
{-# LANGUAGE QuasiQuotes #-}
module PredJson where
import qualified Text.Shakespeare.Text as I
import qualified Data.Text as T
import Data.Aeson.Lens
import Data.Aeson
import Control.Lens

json0' :: String
json0' = T.unpack [I.st|
{
   "title": "production config"
  ,"flag" : true
  ,"langs" : ["c#", "rusxt", "haskell"]
  ,"cnt" : 44
}
|]

json0, json1, json2, json3 :: Value
json0 = json0' ^?! _Value
json1 = json1' ^?! _Value
json2 = json2' ^?! _Value
json3 = json3' ^?! _Value

json1' :: String
json1' = T.unpack [I.st|
{
  "glossary":
  {
    "title": "example glossary",
    "GlossDiv":
    {
      "title": "S",
      "GlossList":
      {
        "GlossEntry":
        {
          "ID": "SGML",
          "SortAs": "SGML",
          "GlossTerm": "Standard Generalized Markup Language",
          "Acronym": "SGML",
          "Abbrev": "ISO 8879:1986",
          "GlossDef":
          {
              "para": "A meta-markup language, used to create markup languages such as DocBook.",
              "GlossSeeAlso": ["GML", "XML"]
          },
          "GlossSee": "markup"
        }
      }
    }
  }
}
|]

json2' :: String
json2' = T.unpack [I.st|
[
   { "firstName"  : "Daniel"
   , "lastName"   : "Diaz"
   , "age"        :  24
   , "likesPizza" :  true
     }
,
   { "firstName"  : "Rose"
   , "lastName"   : "Red"
   , "age"        :  39
   , "likesPizza" :  false
     }
,  { "firstName"  : "John"
   , "lastName"   : "Doe"
   , "age"        :  45
   , "likesPizza" :  false
     }
,  { "firstName"  : "Vladimir"
   , "lastName"   : "Vygodsky"
   , "age"        :  27
   , "likesPizza" :  false
     }
]
|]

json3' :: String
json3' = T.unpack [I.st|
{
   "$schema":"http://json-schema.org/draft-04/schema#",
   "title":"Product set",
   "type":"array",
   "items":{
      "title":"Product",
      "type":"object",
      "properties":{
         "id":{
            "description":"The unique identifier for a product",
            "type":"number"
         },
         "name":{
            "type":"string"
         },
         "price":{
            "type":"number",
            "minimum":0,
            "exclusiveMinimum":true
         },
         "tags":{
            "type":"array",
            "items":{
               "type":"string"
            },
            "minItems":1,
            "uniqueItems":true
         },
         "dimensions":{
            "type":"object",
            "properties":{
               "length":{
                  "type":"number"
               },
               "width":{
                  "type":"number"
               },
               "height":{
                  "type":"number"
               }
            },
            "required":[
               "length",
               "width",
               "height"
            ]
         },
         "warehouseLocation":{
            "description":"Coordinates of the warehouse with the product",
            "$ref":"http://json-schema.org/geo"
         }
      },
      "required":[
         "id",
         "name",
         "price"
      ]
   }
}
|]


data Lang = Lang { lang :: String, score :: Int, year :: Int, name :: String, langType :: LangType }
  deriving (Eq, Show)

langs :: [Lang]
langs =
  [Lang "Haskell" 15  1990 "Simon Peyton-Jones" Func
  , Lang "Rust" 8 2010 "Graydon Hoare" Imperative
  , Lang "Idris" 19 2018 "Edwin Brady" Proof
  , Lang "Ocaml" 13 1996  "Xavier Leroy" Func
  , Lang "Scala" 12 2004 "Martin Odersky" Func
  , Lang "Agda"  19 1999 "Ulf Norell" Proof
  , Lang "Coq" 25 1984 "Gerard Pierre Huet" Proof
  , Lang "Clojure" 13 2007 "Rich Hickey" Func
  , Lang "Purescript" 15 2013 "Phil Freeman" Func
  , Lang "F#" 11 2005 "Don Syme" Func
  , Lang "APL" 8 1966 "Kenneth E. Iverson" Imperative
  ]

data LangType = Proof | Func | Imperative
  deriving (Eq, Ord, Show)

